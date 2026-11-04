module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksFrontier.AlgebraicGeometry.RingedSpace.KFlatResolution
public import StacksFrontier.CategoryTheory.Localization.LeftDerivedByResolutions
public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.HigherDirectImages
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# The derived pullback of modules on a ringed space

For a morphism `f : X ⟶ Y` of ringed spaces, degreewise pullback of complexes of
`𝒪_Y`-modules is not exact, so it does not descend to the derived categories; its left derived
functor `Lf^*` is the right Kan extension of
`K(𝒪_Y) ⥤ D(𝒪_X)` along the localization `K(𝒪_Y) ⥤ D(𝒪_Y)`. This file reduces the existence
of that Kan extension to two statements about complexes of `𝒪_Y`-modules, and records that the
comparison with degreewise pullback is invertible on the resolving complexes.

## Main definitions

* `AlgebraicGeometry.RingedSpace.pullbackToDerivedCategory`: degreewise pullback on the homotopy
  category, followed by localization to the derived category of the source.
* `AlgebraicGeometry.RingedSpace.homotopyObjects`: a class of cochain complexes, read as a class
  of objects of the homotopy category.

## Main results

* `AlgebraicGeometry.RingedSpace.pullbackToDerivedCategory_hasPointwiseLeftDerivedFunctor` and
  `AlgebraicGeometry.RingedSpace.pullbackToDerivedCategory_hasLeftDerivedFunctor`: the left
  derived functor exists, pointwise at every object, as soon as a class `P` of complexes of
  `𝒪_Y`-modules resolves every complex and degreewise pullback carries the quasi-isomorphisms
  between complexes satisfying `P` to quasi-isomorphisms.
* `AlgebraicGeometry.RingedSpace.isIso_app_of_mem`: under the same two hypotheses, the canonical
  comparison from the left derived functor to degreewise pullback is invertible at every complex
  satisfying `P`, so `Lf^*` is computed by pulling back such a resolution degreewise.
* `AlgebraicGeometry.RingedSpace.pullbackToDerivedCategory_hasLeftDerivedFunctor_of_kFlat`: the
  same conclusion for `P` K-flatness, where the resolution hypothesis is discharged, leaving
  only the hypothesis that degreewise pullback preserves quasi-isomorphisms between K-flat
  complexes.

## Implementation notes

The two hypotheses are deliberately phrased for an arbitrary class `P` of cochain complexes
rather than for K-flatness. Nothing below uses a tensor product, so none of the instances that
`Stacks.SheafOfModules.IsKFlat` carries — additivity of `⊗_𝒪` in each variable, the countable
direct sums forming the total complexes, sheafification of abelian groups — appear in them. The
instantiation at `P := Stacks.SheafOfModules.IsKFlat Y.sheaf` is then taken in
`pullbackToDerivedCategory_hasLeftDerivedFunctor_of_kFlat`, where those instances do appear and
where the resolution hypothesis is supplied by
`AlgebraicGeometry.RingedSpace.exists_isKFlat_quasiIso`. What is left over there is the single
statement that degreewise pullback preserves quasi-isomorphisms between K-flat complexes, i.e.
that the pullback of an acyclic K-flat complex is acyclic ([Stacks, Tag 06YS]). Note that
`Stacks.SheafOfModules.IsKFlat Y.sheaf` is a predicate on
`CochainComplex (SheafOfModules (structureSheafRing Y)) ℤ` with no comparison in between, because
`Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf` and `structureSheafRing Y` are the same term.

The derivability of degreewise pullback along a resolving class is
`CategoryTheory.LeftDerivedByResolutions.hasPointwiseLeftDerivedFunctor_of_resolutions`: a class
of objects which resolves every object of a category with a right calculus of fractions is a
left derivability structure, and a functor inverting the weak equivalences between objects of
that class is derivable along it. The quasi-isomorphisms of `K(𝒪_Y)` have a right calculus of
fractions because they are the class attached to the triangulated subcategory of acyclic
complexes.

A class of complexes is turned into a class of objects of the homotopy category by
`homotopyObjects`, i.e. by taking the images under `HomotopyCategory.quotient`; this needs no
invariance of `P` under homotopy equivalence, since the quotient functor is surjective on
objects and full, so both hypotheses transfer to the homotopy category verbatim.

The universe of the derived category of the source is an instance argument rather than fixed to
the standard choice; no derived category of the target is assumed, the localization of `K(𝒪_Y)`
being taken as a variable.

## References

* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
-/

@[expose] public noncomputable section

open CategoryTheory RingedSpaceModuleAdjunction

namespace AlgebraicGeometry.RingedSpace

universe u w

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- Degreewise pullback of complexes of `𝒪_Y`-modules, followed by localization to the derived
category of `𝒪_X`-modules. Its left derived functor is the derived pullback. -/
public def pullbackToDerivedCategory
    [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing X))] :
    HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) :=
  (modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- A class `P` of cochain complexes of `𝒪_Y`-modules, read as the class of those objects of
`K(𝒪_Y)` which are the image of a complex satisfying `P`. -/
public def homotopyObjects
    (P : ObjectProperty (CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ)) :
    ObjectProperty
      (HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) :=
  fun K => ∃ L, P L ∧ (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L = K

/-- The quasi-isomorphisms of the homotopy category of cochain complexes in an abelian category
have a right calculus of fractions, being the class attached to the triangulated subcategory of
acyclic complexes. -/
private lemma hasRightCalculusOfFractions_quasiIso (A : Type*) [Category A] [Abelian A] :
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).HasRightCalculusOfFractions := by
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  infer_instance

/-- The class of objects of `K(𝒪_Y)` attached to a resolving class of complexes resolves every
object of `K(𝒪_Y)`: the quotient functor is surjective on objects, and a morphism of complexes
is a quasi-isomorphism exactly when its homotopy class is one. -/
private lemma hasResolutions_homotopyObjects
    (P : ObjectProperty (CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ))
    (hres : ∀ K : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ,
      ∃ (L : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) (_ : P L) (s : L ⟶ K),
        QuasiIso s)
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) :
    ∃ (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
      (_ : homotopyObjects P M) (s : M ⟶ K),
      HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y))
        (ComplexShape.up ℤ) s := by
  obtain ⟨K₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨L, hL, s, hs⟩ := hres K₀
  exact ⟨_, ⟨L, hL, rfl⟩, (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s, by
    rwa [HomotopyCategory.quotient_map_mem_quasiIso_iff]⟩

/-- Degreewise pullback, followed by localization, inverts the quasi-isomorphisms of `K(𝒪_Y)`
between objects coming from complexes satisfying `P`, as soon as degreewise pullback carries a
quasi-isomorphism between complexes satisfying `P` to a quasi-isomorphism: the quotient functor
is full, so such a morphism of `K(𝒪_Y)` is the homotopy class of a morphism of complexes. -/
private lemma isIso_map_of_homotopyObjects
    [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing X))]
    (P : ObjectProperty (CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ))
    (hinv : ∀ {L L' : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ} (s : L ⟶ L'),
      QuasiIso s → P L → P L' →
      QuasiIso (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map s))
    {K L : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)}
    (s : K ⟶ L)
    (hs : HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y))
      (ComplexShape.up ℤ) s)
    (hK : homotopyObjects P K) (hL : homotopyObjects P L) :
    IsIso ((pullbackToDerivedCategory f).map s) := by
  obtain ⟨K₀, hK₀, rfl⟩ := hK
  obtain ⟨L₀, hL₀, rfl⟩ := hL
  obtain ⟨σ, rfl⟩ := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_surjective s
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff] at hs
  refine Localization.inverts DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    (((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map σ)) ?_
  rw [Functor.mapHomotopyCategory_map]
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 (hinv σ hs hK₀ hL₀)

/-- Degreewise pullback of complexes of `𝒪_Y`-modules, followed by localization to the derived
category of `𝒪_X`-modules, has a pointwise left derived functor at every object, as soon as a
class `P` of complexes of `𝒪_Y`-modules resolves every complex up to quasi-isomorphism and
degreewise pullback carries the quasi-isomorphisms between complexes satisfying `P` to
quasi-isomorphisms.

Taking `P` to be K-flatness, the two hypotheses are [Stacks, Tag 06YF] and [Stacks, Tag 06YS].
-/
public theorem pullbackToDerivedCategory_hasPointwiseLeftDerivedFunctor
    [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing X))]
    (P : ObjectProperty (CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ))
    (hres : ∀ K : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ,
      ∃ (L : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) (_ : P L) (s : L ⟶ K),
        QuasiIso s)
    (hinv : ∀ {L L' : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ} (s : L ⟶ L'),
      QuasiIso s → P L → P L' →
      QuasiIso (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map s)) :
    (pullbackToDerivedCategory f).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) :=
  have := hasRightCalculusOfFractions_quasiIso (SheafOfModules.{u} (structureSheafRing Y))
  LeftDerivedByResolutions.hasPointwiseLeftDerivedFunctor_of_resolutions _ (homotopyObjects P)
    (hasResolutions_homotopyObjects P hres) _
    (isIso_map_of_homotopyObjects f P hinv)

/-- Degreewise pullback of complexes of `𝒪_Y`-modules, followed by localization to the derived
category of `𝒪_X`-modules, has an everywhere-defined left derived functor `Lf^*` under the same
two hypotheses. The derived pullback of [Stacks, Tag 06YJ] is this left derived functor. -/
public theorem pullbackToDerivedCategory_hasLeftDerivedFunctor
    [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing X))]
    (P : ObjectProperty (CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ))
    (hres : ∀ K : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ,
      ∃ (L : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) (_ : P L) (s : L ⟶ K),
        QuasiIso s)
    (hinv : ∀ {L L' : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ} (s : L ⟶ L'),
      QuasiIso s → P L → P L' →
      QuasiIso (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map s)) :
    (pullbackToDerivedCategory f).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) :=
  have := pullbackToDerivedCategory_hasPointwiseLeftDerivedFunctor f P hres hinv
  Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor _ _

/-- On a complex satisfying the resolving class `P`, the canonical comparison from a left derived
functor of degreewise pullback to degreewise pullback is an isomorphism: the derived pullback is
computed by pulling back such a resolution degreewise. -/
public theorem isIso_app_of_mem
    [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing X))]
    (P : ObjectProperty (CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ))
    (hres : ∀ K : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ,
      ∃ (L : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) (_ : P L) (s : L ⟶ K),
        QuasiIso s)
    (hinv : ∀ {L L' : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ} (s : L ⟶ L'),
      QuasiIso s → P L → P L' →
      QuasiIso (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map s))
    {D : Type*} [Category D]
    (L : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ) ⥤ D)
    [L.IsLocalization
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))]
    (LF : D ⥤ DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (α : L ⋙ LF ⟶ pullbackToDerivedCategory f)
    [LF.IsLeftDerivedFunctor α
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))]
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) (hK : P K) :
    IsIso (α.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) :=
  have := hasRightCalculusOfFractions_quasiIso (SheafOfModules.{u} (structureSheafRing Y))
  LeftDerivedByResolutions.isIso_app_of_resolutions _ (homotopyObjects P)
    (hasResolutions_homotopyObjects P hres) _
    (isIso_map_of_homotopyObjects f P hinv)
    L LF α _ ⟨K, hK, rfl⟩

/-- Degreewise pullback of complexes of `𝒪_Y`-modules, followed by localization to the derived
category of `𝒪_X`-modules, has an everywhere-defined left derived functor as soon as degreewise
pullback carries the quasi-isomorphisms between K-flat complexes to quasi-isomorphisms. The
other hypothesis — that K-flat complexes resolve every complex of `𝒪_Y`-modules — is discharged
by `AlgebraicGeometry.RingedSpace.exists_isKFlat_quasiIso`.

The remaining hypothesis follows from [Stacks, Tag 06YS]: the pullback of an acyclic K-flat
complex is acyclic, whence the pullback of a quasi-isomorphism between K-flat complexes is a
quasi-isomorphism, its cone being acyclic and K-flat. -/
public theorem pullbackToDerivedCategory_hasLeftDerivedFunctor_of_kFlat
    [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing X))]
    [HasWeakSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj M).Additive]
    [∀ (K₁ K₂ : HomologicalComplex
        (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)
        (ComplexShape.up ℤ)]
    (hinv : ∀ {L L' : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ} (s : L ⟶ L'),
      QuasiIso s → Stacks.SheafOfModules.IsKFlat Y.sheaf L →
        Stacks.SheafOfModules.IsKFlat Y.sheaf L' →
        QuasiIso (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map s)) :
    (pullbackToDerivedCategory f).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) :=
  pullbackToDerivedCategory_hasLeftDerivedFunctor f (Stacks.SheafOfModules.IsKFlat Y.sheaf)
    (fun K => (exists_isKFlat_quasiIso Y K).imp fun _ ⟨s, hP, hs⟩ => ⟨hP, s, hs⟩)
    hinv

end AlgebraicGeometry.RingedSpace

end
