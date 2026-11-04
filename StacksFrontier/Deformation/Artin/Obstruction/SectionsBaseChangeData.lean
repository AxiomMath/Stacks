module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsObstructionOverBase

/-!
# The base-change data of a deformation situation, as opaque names

The comparisons of Stacks 07YH are statements about seven pieces of data attached to a ring map
`φ : A' → A`, a scheme `t : Spec A' → S` and a module `𝓕` on `q : W → S`: the two base changes
`W_{A'}` and `W_A`, their structure morphisms to `Spec A'` and `Spec A`, the two pullbacks
`𝓕_{A'}` and `𝓕_A` of `𝓕`, and the base-change immersion `i : W_A → W_{A'}`.

Written out, each of those is a `pullback` or a `Scheme.Modules.pullback` of a `pullback.snd`,
and a statement mentioning several of them is a term large enough that an innocuous
definitional comparison — `(ShortComplex.mk f g zero).X₁` against
`(ModuleCat.restrictScalars φ.hom).obj M`, say, buried inside two cohomology modules — exhausts
the heartbeat budget or the recursion limit. This file gives the seven data opaque names, so
that statements about them are small and unification between two such statements is syntactic.
The one place the explicit forms are unfolded is where a comparison already proved in the
explicit spelling is re-stated here, and there the two sides are identical after unfolding.

## Main definitions

* `Deformation.Artin.SectionsSheaf.topScheme`, `topProj`, `topSheaf` — `W_{A'}`, its structure
  morphism to `Spec A'`, and `𝓕_{A'}`.
* `Deformation.Artin.SectionsSheaf.botScheme`, `botProj`, `botSheaf` — `W_A`, its structure
  morphism to `Spec A`, and `𝓕_A`.
* `Deformation.Artin.SectionsSheaf.immersion` — the base-change immersion `i : W_A → W_{A'}`.
* `Deformation.Artin.SectionsSheaf.obstructionBaseChangeIsoData` — the comparison
  `Hⁿ(W_{A'}, 𝓕_{A'} ⊗_{A'} M) ≅ Hⁿ(W_A, 𝓕_A ⊗_A M)` in this spelling.
* `Deformation.Artin.SectionsSheaf.obstructionClassData` — the obstruction element in the
  source's `𝒪_x(M)`, in this spelling.

## Main results

* `Deformation.Artin.SectionsSheaf.obstructionClassData_eq_zero_iff` — **the obstruction element
  in `𝒪_x(I)` vanishes exactly when the one computed on `W_{A'}` does.** With
  `exists_section_iff_obstructionClass_eq_zero` this is condition (iii) of Stacks 07YG for the
  element the source places in `𝒪_x(I)`.

## Implementation notes

The seven names are plain `def`s, not `abbrev`s: a reducible abbreviation is unfolded during
unification and would buy nothing. The `rfl`-lemmas `topScheme_eq` and so on are provided for
the one direction a consumer needs, namely passing to the explicit spelling in which the
geometric inputs are stated.

## References

* [Stacks Project, Tag 07YH](https://stacks.math.columbia.edu/tag/07YH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Deformation.Artin.SectionsSheaf

variable {S : Scheme.{u}} {A' A : CommRingCat.{u}} (φ : A' ⟶ A) (t : Spec A' ⟶ S)
  {W : Scheme.{u}} (q : W ⟶ S) (𝓕 : W.Modules)

/-- `W_{A'} = Spec A' ×_S W`. -/
def topScheme : Scheme.{u} := pullback (Over.mk t).hom q

/-- The structure morphism `W_{A'} → Spec A'`. -/
def topProj : topScheme t q ⟶ Spec A' := pullback.fst (Over.mk t).hom q

/-- `𝓕_{A'}`, the pullback of `𝓕` to `W_{A'}`. -/
def topSheaf : SheafOfModules.{u} (topScheme t q).ringCatSheaf :=
  (Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕

/-- `W_A = Spec A ×_S W`. -/
def botScheme : Scheme.{u} := pullback (quotOver φ t).hom q

/-- The structure morphism `W_A → Spec A`. -/
def botProj : botScheme φ t q ⟶ Spec A := pullback.fst (quotOver φ t).hom q

/-- `𝓕_A`, the pullback of `𝓕` to `W_A`. -/
def botSheaf : SheafOfModules.{u} (botScheme φ t q).ringCatSheaf :=
  (Scheme.Modules.pullback (pullback.snd (quotOver φ t).hom q)).obj 𝓕

/-- The base-change immersion `i : W_A → W_{A'}`. -/
def immersion : botScheme φ t q ⟶ topScheme t q := baseChangeMap q (quotHom φ t)

/-- `topScheme` is the fibre product. -/
theorem topScheme_eq : topScheme t q = pullback (Over.mk t).hom q := rfl

/-- `botScheme` is the fibre product. -/
theorem botScheme_eq : botScheme φ t q = pullback (quotOver φ t).hom q := rfl

/-- `immersion` is the base-change morphism. -/
theorem immersion_eq : immersion φ t q = baseChangeMap q (quotHom φ t) := rfl

section Cohomology

attribute [local instance] HasDerivedCategory.standard

/-- **`Hⁿ(W_{A'}, 𝓕_{A'} ⊗_{A'} M) ≅ Hⁿ(W_A, 𝓕_A ⊗_A M)`**, in the opaque spelling: the
obstruction module over `A'` at an `A`-module is the obstruction module over `A`. -/
def obstructionBaseChangeIsoData (hi : IsClosedImmersion (immersion φ t q)) (n : ℕ)
    (M : ModuleCat.{u} A) :
    ((cohomologyDeltaFunctor (topProj t q)).functor n).obj
        ((tensorSheafFunctor (topProj t q) (topSheaf t q 𝓕)).obj
          ((ModuleCat.restrictScalars φ.hom).obj M)) ≅
      (ModuleCat.restrictScalars φ.hom).obj
        (((cohomologyDeltaFunctor (botProj φ t q)).functor n).obj
          ((tensorSheafFunctor (botProj φ t q) (botSheaf φ t q 𝓕)).obj M)) :=
  obstructionBaseChangeIso φ t q 𝓕 hi n M

/-- `obstructionBaseChangeIsoData` with the `A'`-module named separately, so that a consumer
whose module arises as the first term of a short complex uses it with no defeq search. -/
def obstructionBaseChangeIsoDataOf (hi : IsClosedImmersion (immersion φ t q)) (n : ℕ)
    (M : ModuleCat.{u} A) (M' : ModuleCat.{u} A')
    (hM : M' = (ModuleCat.restrictScalars φ.hom).obj M) :
    ((cohomologyDeltaFunctor (topProj t q)).functor n).obj
        ((tensorSheafFunctor (topProj t q) (topSheaf t q 𝓕)).obj M') ≅
      (ModuleCat.restrictScalars φ.hom).obj
        (((cohomologyDeltaFunctor (botProj φ t q)).functor n).obj
          ((tensorSheafFunctor (botProj φ t q) (botSheaf φ t q 𝓕)).obj M)) :=
  eqToIso (congrArg (fun N => ((cohomologyDeltaFunctor (topProj t q)).functor n).obj
      ((tensorSheafFunctor (topProj t q) (topSheaf t q 𝓕)).obj N)) hM) ≪≫
    obstructionBaseChangeIsoData φ t q 𝓕 hi n M

variable {M : ModuleCat.{u} A} {Y₂ Y₃ : ModuleCat.{u} A'}

/-- **The obstruction element `o_x(A')` in the source's obstruction module**, in the opaque
spelling: for a short exact sequence of `A'`-modules whose first term is an `A`-module — the
sequence `0 → I → A' → A → 0` of a deformation situation — the obstruction element of a
section, read in `𝒪_x(M) = H¹(W_A, 𝓕_A ⊗_A M)`. -/
def obstructionClassData
    (hF : AlgebraicGeometry.IsFlatOver (topProj t q).toLRSHom.toShHom (topSheaf t q 𝓕))
    (hi : IsClosedImmersion (immersion φ t q))
    {f : (ModuleCat.restrictScalars φ.hom).obj M ⟶ Y₂} {g : Y₂ ⟶ Y₃} {zero : f ≫ g = 0}
    (hSq : (ShortComplex.mk f g zero).ShortExact)
    (x : (((cohomologyDeltaFunctor (topProj t q)).functor 0).obj
      ((tensorSheafFunctor (topProj t q) (topSheaf t q 𝓕)).obj Y₃) : Type u)) :=
  (obstructionBaseChangeIsoDataOf φ t q 𝓕 hi 1 M (ShortComplex.mk f g zero).X₁ rfl).hom
    (obstructionClass (topProj t q) (topSheaf t q 𝓕) hF hSq x)

/-- **The obstruction element in the source's `𝒪_x(I)` vanishes exactly when the one computed
on `W_{A'}` does.** The comparison is an isomorphism, so with
`exists_section_iff_obstructionClass_eq_zero` this is condition (iii) of Stacks 07YG for the
element the source places in `𝒪_x(I)`: it vanishes if and only if the section of `𝓕_A` lifts to
a section of `𝓕_{A'}`. -/
theorem obstructionClassData_eq_zero_iff
    (hF : AlgebraicGeometry.IsFlatOver (topProj t q).toLRSHom.toShHom (topSheaf t q 𝓕))
    (hi : IsClosedImmersion (immersion φ t q))
    {f : (ModuleCat.restrictScalars φ.hom).obj M ⟶ Y₂} {g : Y₂ ⟶ Y₃} {zero : f ≫ g = 0}
    (hSq : (ShortComplex.mk f g zero).ShortExact)
    (x : (((cohomologyDeltaFunctor (topProj t q)).functor 0).obj
      ((tensorSheafFunctor (topProj t q) (topSheaf t q 𝓕)).obj Y₃) : Type u)) :
    obstructionClassData φ t q 𝓕 hF hi hSq x = 0 ↔
      obstructionClass (topProj t q) (topSheaf t q 𝓕) hF hSq x = 0 := by
  unfold obstructionClassData
  exact iso_hom_eq_zero_iff _ _

end Cohomology

end Deformation.Artin.SectionsSheaf

end
