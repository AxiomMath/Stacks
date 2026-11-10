module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.IdealOfGlobalSections
public import StacksFrontier.RingTheory.Cech.PresheafComplexQuasiIso
import StacksCore.Tactic.StacksAttribute

/-!
# The object of Tag 099E: the sheafified presheaf of Čech complexes

Let `(𝒞, 𝒪)` be a ringed site and let `f_1, …, f_r` be global sections of `𝒪`. This file builds

`K(f_1, …, f_r) ⟶ 𝒪`

in the category of complexes of sheaves of `𝒪`-modules, as **the sheafification of the presheaf
of complexes**

`U' ↦ K(𝒪(U'), (f_1|_{U'}, …, f_r|_{U'}))`

of `StacksFrontier/RingTheory/Cech/PresheafComplex.lean`, together with the sheafification of that
presheaf complex's augmentation onto `𝒪`.

This is the construction [Stacks, Tag 099E] performs: for an object `U` and a finitely generated
ideal `I ⊆ ℐ(U)` generating `ℐ|_U`, the complex of presheaves `K_{U, I}^\bullet` on `𝒞/U` and its
sheafification. The ideal `I` enters only through a finite family of its generators, which is
also all the construction uses — and all it *can* use, a choice of generators functorial in the
ring being impossible (`Stacks.FunctorialCechFamily.isEmpty_functorialGenerators`). A family of
sections over `U` is a family of global sections on the slice `𝒞/U`
(`AlgebraicGeometry.RingedSite.globalSectionOfSection`), so the statements here, applied to the
slice, are the statements of the tag.

## Main definitions

* `AlgebraicGeometry.RingedSite.cechPresheafComplex`: the `ℤ`-indexed presheaf of Čech complexes
  of a finite family of global sections.
* `AlgebraicGeometry.RingedSite.sheafifiedCech`: **the object of [Stacks, Tag 099E]** — the
  sheafification of that presheaf of complexes.
* `AlgebraicGeometry.RingedSite.sheafifiedCechAugmentation`: **the map `K ⟶ 𝒪`.**

## Main results

* `AlgebraicGeometry.RingedSite.quasiIso_sheafifiedCechRestrict`: **the comparison of the objects
  of a family and of a subfamily spanning the same ideal of sections over every object is a
  quasi-isomorphism**, and `AlgebraicGeometry.RingedSite.sheafifiedCechRestrict_comp_augmentation`
  that it is a map over `𝒪`.

## Implementation notes

Sheafification of presheaves of modules is exact — it preserves finite limits because
sheafification is left exact and finite colimits because it is a left adjoint — hence preserves
homology, which is what carries a quasi-isomorphism of presheaf complexes to one of sheaf
complexes. That is the step the comparison in the derived category of each ring of sections cannot
make, and the reason the construction is performed on presheaves and sheafified rather than
assembled from the sheaf-level Čech complexes.

The augmentation is assembled from four pieces: the extension of the `ℕ`-indexed presheaf
augmentation to the `ℤ`-indexed complex, the identification of the extension of an object placed
in degree zero with that object placed in degree zero, the comparison of sheafification with the
placement in degree zero, and the counit of the sheafification adjunction at the unit sheaf of
modules — which is invertible, `𝒪` being a sheaf already.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [Stacks Project, Tag 099E](https://stacks.math.columbia.edu/tag/099E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

section Object

variable (X : RingedSite.{u, u, u})
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] {r s : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- Sheafification of presheaves of `𝒪`-modules. -/
abbrev moduleSheafificationFunctor :
    PresheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj ⥤
      SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  PresheafOfModules.sheafification.{u} (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj)

/-- Sheafification of presheaves of `𝒪`-modules is an additive functor. -/
instance additive_moduleSheafification : (moduleSheafificationFunctor X).Additive :=
  (PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj)).left_adjoint_additive

/-- Sheafification of presheaves of `𝒪`-modules preserves finite colimits. -/
instance preservesFiniteColimits_moduleSheafification :
    PreservesFiniteColimits (moduleSheafificationFunctor X) :=
  have : PreservesColimitsOfSize.{0, 0} (moduleSheafificationFunctor X) :=
    (PresheafOfModules.sheafificationAdjunction.{u}
      (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj)).leftAdjoint_preservesColimits
  inferInstance

/-- **Sheafification of presheaves of modules preserves homology**, being exact: it preserves
finite limits because sheafification is left exact, and finite colimits because it is a left
adjoint. -/
instance preservesHomology_moduleSheafification :
    (moduleSheafificationFunctor X).PreservesHomology :=
  Functor.preservesHomologyOfExact _

/-- The family of global sections, read over each object. -/
abbrev cechFamily (V : X.Cᵒᵖ) (i : Fin r) : X.O.obj.obj V := globalSectionVal (f i) V

omit [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] in
/-- The restrictions of a global section agree with the values of the family. -/
theorem cechFamily_map {V W : X.Cᵒᵖ} (a : V ⟶ W) (i : Fin r) :
    (X.O.obj.map a).hom (cechFamily X f V i) = cechFamily X f W i :=
  globalSectionVal_map (f i) a

/-- The presheaf of Čech complexes of a finite family of global sections of `𝒪`: over each
object it is the extended alternating Čech complex of the ring of sections at the restrictions of
the family, and in degrees `< 0` it is zero.

The type is written with `(ringSheaf X).obj` for the presheaf of rings, which is
`X.O.obj ⋙ forget₂ CommRingCat RingCat` only after `CategoryTheory.sheafCompose` is unfolded.
Keeping to one spelling matters: `rw` and `simp` check their motives at a transparency at which
that definition does not unfold, so a statement mixing the two is refused even though it is
type-correct. Everything below is therefore phrased through these definitions, each of which is
opaque and has its type in this spelling, rather than through the underlying terms of
`Stacks.CechPresheaf`. -/
def cechPresheafComplex :
    CochainComplex (PresheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj) ℤ :=
  Stacks.CechPresheaf.cechPresheafComplex X.O.obj (cechFamily X f) (cechFamily_map X f)

/-- **The augmentation of the presheaf of Čech complexes onto `𝒪`.** -/
def cechPresheafAugmentation :
    cechPresheafComplex X f ⟶ (CochainComplex.singleFunctor _ 0).obj
      (PresheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj) :=
  Stacks.CechPresheaf.cechPresheafAugmentation X.O.obj (cechFamily X f) (cechFamily_map X f)

/-- **The object of [Stacks, Tag 099E]**: the sheafification of the presheaf of complexes
`U' ↦ K(𝒪(U'), (f_1|_{U'}, …, f_r|_{U'}))`. -/
abbrev sheafifiedCech :
    CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ℤ :=
  ((moduleSheafificationFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (cechPresheafComplex X f)

/-- **The map `K ⟶ 𝒪` of [Stacks, Tag 099E].** It is the sheafification of the augmentation of
the presheaf of Čech complexes, with the sheafification of `𝒪` read as `𝒪` through the counit of
the sheafification adjunction, which is invertible because `𝒪` is a sheaf already.

The target is `𝒪` placed in degree zero, which is
`AlgebraicGeometry.RingedSite.structureSheafComplex`, spelled out here so that the import closure
of this file does not have to contain the internal-Hom machinery that names it. -/
def sheafifiedCechAugmentation :
    sheafifiedCech X f ⟶
      (CochainComplex.singleFunctor
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  ((moduleSheafificationFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (cechPresheafAugmentation X f) ≫
    ((moduleSheafificationFunctor X).mapCochainComplexSingleFunctor 0).hom.app
      (PresheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj) ≫
    (CochainComplex.singleFunctor _ 0).map
      ((PresheafOfModules.sheafificationAdjunction.{u}
          (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj)).counit.app
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))

end Object

section Restrict

variable (X : RingedSite.{u, u, u})
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] {r s : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  (g : Fin s → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

omit [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] in
/-- The subfamily condition, read over each object. -/
theorem cechFamily_order_embedding (e : Fin r ↪o Fin s) (he : ∀ i, g (e i) = f i)
    (V : X.Cᵒᵖ) (i : Fin r) : cechFamily X g V (e i) = cechFamily X f V i :=
  congrArg (fun h => globalSectionVal h V) (he i)

/-- The restriction map onto a subfamily, on the presheaves of Čech complexes. -/
def cechPresheafRestrict (e : Fin r ↪o Fin s) (he : ∀ i, g (e i) = f i) :
    cechPresheafComplex X g ⟶ cechPresheafComplex X f :=
  Stacks.CechPresheaf.cechPresheafRestrict X.O.obj (cechFamily X f) (cechFamily_map X f)
    (cechFamily X g) (cechFamily_map X g) e (cechFamily_order_embedding X f g e he)

omit [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] in
/-- **The restriction map of the presheaves of Čech complexes is a map over `𝒪`.** -/
theorem cechPresheafRestrict_comp_augmentation (e : Fin r ↪o Fin s)
    (he : ∀ i, g (e i) = f i) :
    cechPresheafRestrict X f g e he ≫ cechPresheafAugmentation X f =
      cechPresheafAugmentation X g :=
  Stacks.CechPresheaf.cechPresheafRestrict_comp_augmentation X.O.obj
    (cechFamily X f) (cechFamily_map X f) (cechFamily X g) (cechFamily_map X g) e
    (cechFamily_order_embedding X f g e he)

omit [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] in
/-- **The restriction map of the presheaves of Čech complexes is a quasi-isomorphism as soon as
the two families span the same ideal of sections over every object.** -/
theorem quasiIso_cechPresheafRestrict (e : Fin r ↪o Fin s) (he : ∀ i, g (e i) = f i)
    (hspan : ∀ V : X.Cᵒᵖ,
      Ideal.span (Set.range (restrictGlobalSections X g V)) =
        Ideal.span (Set.range (restrictGlobalSections X f V))) :
    QuasiIso (cechPresheafRestrict X f g e he) := by
  exact (HomologicalComplex.quasiIso_extendMap_iff _ ComplexShape.embeddingUpNat).2
    (Stacks.CechPresheaf.quasiIso_cechPresheafRestrictNat X.O.obj _ _ _ _ e _ fun V => hspan V)

/-- The comparison of the objects of a family and of a subfamily, obtained by sheafifying the
restriction map of the presheaves of Čech complexes. -/
def sheafifiedCechRestrict (e : Fin r ↪o Fin s) (he : ∀ i, g (e i) = f i) :
    sheafifiedCech X g ⟶ sheafifiedCech X f :=
  ((moduleSheafificationFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).map
    (cechPresheafRestrict X f g e he)

/-- **The comparison is a quasi-isomorphism as soon as the two families span the same ideal of
sections over every object.** The restriction map of the presheaves of Čech complexes is a
quasi-isomorphism there, and sheafification preserves homology. -/
theorem quasiIso_sheafifiedCechRestrict (e : Fin r ↪o Fin s) (he : ∀ i, g (e i) = f i)
    (hspan : ∀ V : X.Cᵒᵖ,
      Ideal.span (Set.range (restrictGlobalSections X g V)) =
        Ideal.span (Set.range (restrictGlobalSections X f V))) :
    QuasiIso (sheafifiedCechRestrict X f g e he) := by
  have := quasiIso_cechPresheafRestrict X f g e he hspan
  exact HomologicalComplex.quasiIso_map_of_preservesHomology (cechPresheafRestrict X f g e he)
    (moduleSheafificationFunctor X)

omit [HasSheafify X.J AddCommGrpCat.{u}] in
/-- **The comparison is a map over `𝒪`.** -/
theorem sheafifiedCechRestrict_comp_augmentation (e : Fin r ↪o Fin s)
    (he : ∀ i, g (e i) = f i) :
    sheafifiedCechRestrict X f g e he ≫ sheafifiedCechAugmentation X f =
      sheafifiedCechAugmentation X g := by
  dsimp only [sheafifiedCechAugmentation, sheafifiedCechRestrict]
  rw [← Functor.map_comp_assoc, cechPresheafRestrict_comp_augmentation]

end Restrict

end AlgebraicGeometry.RingedSite

end
