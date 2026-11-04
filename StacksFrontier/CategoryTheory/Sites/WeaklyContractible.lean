module

public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible.Objects
public import StacksCore.Tactic.StacksAttribute

/-!
# Weakly contractible objects, and "enough `P` objects"

In a site `C`:

1. an object `U` is *weakly contractible* if every surjection of sheaves of sets on `C` is
   surjective on sections over `U`; equivalently, for every covering `{U_i → U}` the morphism
   `π^# : ∐ h_{U_i}^# ⟶ h_U^#` admits a section;
2. `C` has *enough weakly contractible objects* if every object has a covering by weakly
   contractible ones;
3. more generally, for a property `P` of objects, `C` has *enough `P` objects* if every
   object has a covering by objects with `P`.

## Main definitions

* `CategoryTheory.GrothendieckTopology.IsWeaklyContractible`: weakly contractible objects.
* `CategoryTheory.GrothendieckTopology.HasEnoughObjects`: a site has enough `P` objects.
* `CategoryTheory.GrothendieckTopology.HasEnoughWeaklyContractibleObjects`: a site has enough
  weakly contractible objects.

## Main results

* `CategoryTheory.GrothendieckTopology.isWeaklyContractible_iff_hasRightInverse`: the two
  characterizations of weakly contractible objects agree.
* `CategoryTheory.GrothendieckTopology.isWeaklyContractible_bot`: for the trivial topology every
  object is weakly contractible.

## References

* [Stacks Project, Tag 090K](https://stacks.math.columbia.edu/tag/090K)
* [Stacks Project, Tag 090L](https://stacks.math.columbia.edu/tag/090L)
-/

@[expose] public section

open CategoryTheory Limits Opposite

namespace CategoryTheory.GrothendieckTopology

universe v u
variable {C : Type u} [Category.{v} C] [Small.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J (Type v)]

/-- An object `U` of a site `C` is *weakly contractible* if every surjection of sheaves of sets on
`C` is surjective on sections over `U`. -/
@[stacks 090L "(1)"]
def IsWeaklyContractible (U : C) : Prop :=
  ∀ (F G : Sheaf J (Type v)) (φ : F ⟶ G),
    Sheaf.IsLocallySurjective φ →
      Function.Surjective ((sheafToPresheaf J (Type v)).map φ |>.app (op U))

/-- An object `U` is weakly contractible if and only if for every covering `{U_i → U}` the
morphism `π^# : ∐ h_{U_i}^# ⟶ h_U^#` admits a right inverse. -/
theorem isWeaklyContractible_iff_hasRightInverse (U : C) :
    IsWeaklyContractible J U ↔
      ∀ (I : Type v) (Ui : I → C) (f : ∀ i, Ui i ⟶ U),
        Sieve.ofArrows Ui f ∈ J U → Stacks.WeaklyContractible.HasRightInverse J Ui f :=
  (hasRightInverse_iff_isLocallySurjective_surjective (U := U) J).symm

/-- A site `C` *has enough `P` objects*, for a property `P` of objects of `C`, if every object
`U` of `C` has a covering `{U_i → U}` with `P (U_i)` for all `i`. -/
@[stacks 090L "(3)"]
def HasEnoughObjects (P : ObjectProperty C) : Prop :=
  ∀ U : C,
    ∃ (I : Type v) (Ui : I → C) (f : ∀ i, Ui i ⟶ U), Sieve.ofArrows Ui f ∈ J U ∧ ∀ i, P (Ui i)

/-- A site `C` *has enough weakly contractible objects* if every object has a covering by weakly
contractible objects, i.e. if it has enough `IsWeaklyContractible` objects. -/
@[stacks 090L "(2)"]
def HasEnoughWeaklyContractibleObjects : Prop :=
  HasEnoughObjects J (IsWeaklyContractible J)

omit [Small.{v} C] [HasSheafify J (Type v)] in
/-- For the trivial topology `⊥` on `C`, every object of `C` is weakly contractible. -/
theorem isWeaklyContractible_bot [HasSheafify (⊥ : GrothendieckTopology C) (Type v)] (U : C) :
    IsWeaklyContractible (⊥ : GrothendieckTopology C) U := by
  intro F G φ hφ s
  have h : Presheaf.imageSieve φ.hom s = ⊤ := hφ.imageSieve_mem s
  obtain ⟨t, ht⟩ : (Presheaf.imageSieve φ.hom s).arrows (𝟙 U) := by
    rw [h]; trivial
  exact ⟨t, by simpa using ht⟩

end CategoryTheory.GrothendieckTopology
