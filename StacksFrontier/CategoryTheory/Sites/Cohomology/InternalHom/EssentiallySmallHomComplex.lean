module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftFiniteColimits
public import StacksFrontier.AlgebraicGeometry.Topologies.GlobalPresentationComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.Bifunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallInternalHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.QuasiIsoInvariance

/-!
# The internal Hom complex on an essentially small ringed site, at the module universe

Let `X` be a ringed site whose objects form a type in a universe `c` while its morphisms, its
structure sheaf and its modules live in `u`, as for the small étale site of a scheme or of an
algebraic space, a `AlgebraicGeometry.RingedSite.{u + 1, u, u}`. The internal Hom complex
`AlgebraicGeometry.RingedSite.sheafHomComplex X L M` of two complexes of `O`-modules with sections
in `Type u` has its sections in `Type (max c u)`: in degree `n` over `U` they are the degree-`n`
cochains between the restrictions of `L` and `M` to the slice site over `U`, and a morphism of
sheaves on that slice is a family indexed by its objects. So the internal Hom complex is not a
complex of `SheafOfModules.{u}`, and the derived internal Hom it computes does not land in the
derived category the other derived functors of the site land in.

That raise is an artefact of the construction as soon as the site is essentially `u`-small,
which the small étale site of an algebraic space is: the sections are then `u`-small, so every
term of the complex descends to the module universe `u` (`Stacks.SheafOfModules.sheafShrink`),
and since raising the universe of the sections is fully faithful the differentials descend too.
This file carries that out and records Stacks 0A95 for the descended complex.

## Main definitions

* `CategoryTheory.Functor.FullyFaithful.liftCochainComplex`: a cochain complex all of whose
  terms lie, up to chosen isomorphisms, in the image of a fully faithful additive functor, read
  as a cochain complex in its source; `liftCochainComplexIso` identifies its image with the
  original complex, and `liftCochainComplexMap` lifts morphisms.
* `AlgebraicGeometry.RingedSite.sheafHomComplexSmall`: the internal Hom complex
  `SheafHom^•(L, M)` as a cochain complex of `SheafOfModules.{u}`.
* `AlgebraicGeometry.RingedSite.homMapSmall`: its functoriality, contravariant in `L` and
  covariant in `M`.

## Main results

* `AlgebraicGeometry.RingedSite.sheafHomComplexSmallIso`: the universe lift of
  `sheafHomComplexSmall X L M` is `(sheafHomComplex X L M).obj`, so this is that internal Hom
  complex and not a second construction.
* `AlgebraicGeometry.RingedSite.homMapSmall_quasiIso`: Stacks 0A95 for `sheafHomComplexSmall`.

## Implementation notes

Quasi-isomorphy descends along the universe lift because the lift is exact
(`Stacks.SheafOfModules.preservesFiniteLimits_moduleULift` and
`Stacks.SheafOfModules.preservesFiniteColimits_moduleULift`), hence preserves homology, and
reflects isomorphisms, being fully faithful. The universe of the lift is taken to be `max c u`,
the universe of the internal Hom complex, rather than `c`: the left-exactness statement is
stated at that spelling, and the two are distinct constants of `ULift` when `u` exceeds `c`.

No tag is placed on `homMapSmall_quasiIso`. Stacks 0A95 is carried by
`AlgebraicGeometry.RingedSite.homMap_quasiIso`, which this statement is a reading of, in the
smaller universe, of the same morphism of complexes.

## References

* [Stacks Project, Tag 0A95](https://stacks.math.columbia.edu/tag/0A95)
* [Stacks Project, Tag 0A8X](https://stacks.math.columbia.edu/tag/0A8X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

universe c u

namespace CategoryTheory.Functor.FullyFaithful

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  {F : C ⥤ D} [F.Additive] (hF : F.FullyFaithful)

/-- A cochain complex in `D` whose terms are, through chosen isomorphisms `e n`, images of
objects `Y n` under a fully faithful additive functor `F : C ⥤ D`, read as a cochain complex in
`C`: its differentials are the preimages of the conjugated differentials. -/
def liftCochainComplex (K : CochainComplex D ℤ) (Y : ℤ → C) (e : ∀ n, F.obj (Y n) ≅ K.X n) :
    CochainComplex C ℤ where
  X := Y
  d i j := hF.preimage ((e i).hom ≫ K.d i j ≫ (e j).inv)
  shape i j h := by
    rw [K.shape i j h]
    exact hF.map_injective (by simp)
  d_comp_d' i j k _ _ := hF.map_injective (by simp)

/-- The image of `liftCochainComplex` under `F` is the original complex. -/
def liftCochainComplexIso (K : CochainComplex D ℤ) (Y : ℤ → C)
    (e : ∀ n, F.obj (Y n) ≅ K.X n) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (hF.liftCochainComplex K Y e) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents e (fun i j _ => by simp [liftCochainComplex])

/-- The degree-`n` component of `liftCochainComplexIso` is `(e n).hom`. -/
@[simp]
theorem liftCochainComplexIso_hom_f (K : CochainComplex D ℤ) (Y : ℤ → C)
    (e : ∀ n, F.obj (Y n) ≅ K.X n) (n : ℤ) :
    (hF.liftCochainComplexIso K Y e).hom.f n = (e n).hom := rfl

/-- The degree-`n` component of the inverse of `liftCochainComplexIso` is `(e n).inv`. -/
@[simp]
theorem liftCochainComplexIso_inv_f (K : CochainComplex D ℤ) (Y : ℤ → C)
    (e : ∀ n, F.obj (Y n) ≅ K.X n) (n : ℤ) :
    (hF.liftCochainComplexIso K Y e).inv.f n = (e n).inv := rfl

variable {K K' K'' : CochainComplex D ℤ} {Y Y' Y'' : ℤ → C} (e : ∀ n, F.obj (Y n) ≅ K.X n)
  (e' : ∀ n, F.obj (Y' n) ≅ K'.X n) (e'' : ∀ n, F.obj (Y'' n) ≅ K''.X n)

/-- A morphism of cochain complexes in `D` between complexes of the form of
`liftCochainComplex`, read as a morphism of the lifted complexes. -/
def liftCochainComplexMap (φ : K ⟶ K') :
    hF.liftCochainComplex K Y e ⟶ hF.liftCochainComplex K' Y' e' where
  f n := hF.preimage ((e n).hom ≫ φ.f n ≫ (e' n).inv)
  comm' i j _ := hF.map_injective (by simp [liftCochainComplex])

/-- The image of `liftCochainComplexMap φ` under `F` is `φ`, conjugated by the identifications
of `liftCochainComplexIso`. -/
theorem map_liftCochainComplexMap (φ : K ⟶ K') :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (hF.liftCochainComplexMap e e' φ) =
      (hF.liftCochainComplexIso K Y e).hom ≫ φ ≫ (hF.liftCochainComplexIso K' Y' e').inv := by
  ext n
  simp [liftCochainComplexMap]

/-- `liftCochainComplexMap` sends the identity of `K` to the identity of the lifted complex. -/
theorem liftCochainComplexMap_id :
    hF.liftCochainComplexMap e e (𝟙 K) = 𝟙 _ := by
  ext n
  exact hF.map_injective (by simp [liftCochainComplexMap, liftCochainComplex])

/-- `liftCochainComplexMap` sends a composite `φ ≫ ψ` to the composite of the lifts. -/
theorem liftCochainComplexMap_comp (φ : K ⟶ K') (ψ : K' ⟶ K'') :
    hF.liftCochainComplexMap e e'' (φ ≫ ψ) =
      hF.liftCochainComplexMap e e' φ ≫ hF.liftCochainComplexMap e' e'' ψ := by
  ext n
  exact hF.map_injective (by simp [liftCochainComplexMap, liftCochainComplex])

end CategoryTheory.Functor.FullyFaithful

namespace CategoryTheory.Functor.FullyFaithful

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  {F : C ⥤ D} [F.Additive] (hF : F.FullyFaithful)
  {K K' : CochainComplex D ℤ} {Y Y' : ℤ → C} (e : ∀ n, F.obj (Y n) ≅ K.X n)
  (e' : ∀ n, F.obj (Y' n) ≅ K'.X n)

/-- A morphism of complexes of the form of `liftCochainComplex` is a quasi-isomorphism exactly
when its lift is, for a fully faithful additive functor between abelian categories which
preserves homology. -/
theorem quasiIso_liftCochainComplexMap_iff [F.PreservesHomology]
    (φ : K ⟶ K') : QuasiIso (hF.liftCochainComplexMap e e' φ) ↔ QuasiIso φ := by
  have : F.Full := hF.full
  have : F.Faithful := hF.faithful
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ F, map_liftCochainComplexMap]
  exact quasiIso_iff_of_arrow_mk_iso _ φ
    (Arrow.isoMk (hF.liftCochainComplexIso K Y e) (hF.liftCochainComplexIso K' Y' e') (by simp))

end CategoryTheory.Functor.FullyFaithful

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C]

/-- Sheaves of modules with sections in `Type u` on a slice of an essentially `u`-small site are
locally `u`-small: they embed faithfully in presheaves of modules on that slice, which is again
essentially `u`-small. -/
instance locallySmall_sheafOfModules_over (U : X.C) :
    LocallySmall.{u} (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) := by
  have := Stacks.essentiallySmall_over.{u} U
  have := Stacks.locallySmall_presheafOfModules_of_essentiallySmall.{u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).obj
  exact locallySmall_of_faithful.{u} (SheafOfModules.forget _)

variable (L M : CochainComplex
  (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **The sections of the terms of the internal Hom complex are `u`-small** on an essentially
`u`-small site. In degree `n` over `U` they are the degree-`n` cochains between the restrictions
of `L` and `M` to the slice over `U`
(`AlgebraicGeometry.RingedSite.SheafHomComplex.sectionsEquiv`), a product indexed by the countable
type of triplets of `u`-small sets of morphisms. -/
instance small_sheafHomComplex_X (n : ℤ) (U : X.Cᵒᵖ) :
    Small.{u} (((sheafHomComplex X L M).obj.X n).val.obj U) := by
  have : Small.{u} (Triplet n) := small_of_injective
    (f := fun T : Triplet n => (ULift.up.{u} T.p, ULift.up.{u} T.q)) (by
      rintro ⟨p, q, h⟩ ⟨p', q', h'⟩ hh
      simp only [Prod.mk.injEq, ULift.up.injEq] at hh
      obtain ⟨rfl, rfl⟩ := hh
      rfl)
  have : Small.{u} (Cochain (restrictComplex X L U.unop) (restrictComplex X M U.unop) n) :=
    inferInstanceAs (Small.{u} (∀ T : Triplet n, _ ⟶ _))
  exact small_of_injective ((sheafHomComplex X L M).sectionsEquiv U.unop n).injective

/-- **The internal Hom complex `SheafHom^•(L, M)` as a cochain complex of `O`-modules with sections
in `Type u`**, on an essentially `u`-small ringed site. Its terms are the terms of
`(sheafHomComplex X L M).obj` with their `u`-small sections read in `Type u`, and its
differentials are the ones of that complex, brought down by full faithfulness of the universe
lift. -/
def sheafHomComplexSmall :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  (Stacks.SheafOfModules.moduleULiftFullyFaithful.{max c u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).liftCochainComplex
    (sheafHomComplex X L M).obj
    (fun n => Stacks.SheafOfModules.sheafShrink.{u, max c u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ((sheafHomComplex X L M).obj.X n))
    (fun n => Stacks.SheafOfModules.sheafShrinkIso.{u, max c u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ((sheafHomComplex X L M).obj.X n))

/-- **The universe lift of `sheafHomComplexSmall X L M` is the internal Hom complex**
`(sheafHomComplex X L M).obj`. -/
def sheafHomComplexSmallIso :
    ((Stacks.SheafOfModules.moduleULift.{max c u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (sheafHomComplexSmall X L M) ≅
      (sheafHomComplex X L M).obj :=
  (Stacks.SheafOfModules.moduleULiftFullyFaithful.{max c u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).liftCochainComplexIso _ _ _

variable {L M} {L' M' L'' M'' : CochainComplex
  (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- The morphism of internal Hom complexes `SheafHom^•(L, M) ⟶ SheafHom^•(L', M')` induced by
`k : L' ⟶ L` and `m : M ⟶ M'`, at the module universe of the site: the morphism
`AlgebraicGeometry.RingedSite.homMap` read through `sheafHomComplexSmallIso`. -/
def homMapSmall (k : L' ⟶ L) (m : M ⟶ M') :
    sheafHomComplexSmall X L M ⟶ sheafHomComplexSmall X L' M' :=
  (Stacks.SheafOfModules.moduleULiftFullyFaithful.{max c u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).liftCochainComplexMap _ _ (homMap X k m)

/-- The universe lift of `homMapSmall X k m` is `homMap X k m`. -/
theorem map_homMapSmall (k : L' ⟶ L) (m : M ⟶ M') :
    ((Stacks.SheafOfModules.moduleULift.{max c u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (homMapSmall X k m) =
      (sheafHomComplexSmallIso X L M).hom ≫ homMap X k m ≫
        (sheafHomComplexSmallIso X L' M').inv :=
  Functor.FullyFaithful.map_liftCochainComplexMap _ _ _ _

/-- `homMapSmall` sends the pair of identities of `L` and `M` to the identity of
`sheafHomComplexSmall X L M`. -/
theorem homMapSmall_id (L M : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    homMapSmall X (𝟙 L) (𝟙 M) = 𝟙 _ := by
  rw [homMapSmall, homMap_id]
  exact Functor.FullyFaithful.liftCochainComplexMap_id _ _

/-- `homMapSmall` is functorial: contravariantly in the first variable and covariantly in the
second, `homMapSmall X (k' ≫ k) (m ≫ m')` is `homMapSmall X k m ≫ homMapSmall X k' m'`. -/
theorem homMapSmall_comp (k : L' ⟶ L) (k' : L'' ⟶ L') (m : M ⟶ M') (m' : M' ⟶ M'') :
    homMapSmall X (k' ≫ k) (m ≫ m') = homMapSmall X k m ≫ homMapSmall X k' m' := by
  rw [homMapSmall, ← homMap_comp]
  exact Functor.FullyFaithful.liftCochainComplexMap_comp _ _ _ _ _ _

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{max c u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max c u}]

omit [EssentiallySmall.{u} X.C] [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Raising the universe of the sections of a sheaf of `O`-modules from `u` to `max c u`
preserves homology: it is additive, left exact and right exact. -/
theorem preservesHomology_moduleULift :
    (Stacks.SheafOfModules.moduleULift.{max c u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).PreservesHomology := by
  have := Stacks.SheafOfModules.preservesFiniteLimits_moduleULift
    (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  have := Stacks.SheafOfModules.preservesFiniteColimits_moduleULift.{max c u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  infer_instance

/-- **Stacks 0A95 at the module universe of the site.** A quasi-isomorphism `l : L' ⟶ L` and a
quasi-isomorphism `i : I' ⟶ I` between K-injective complexes of `O`-modules induce a
quasi-isomorphism `SheafHom^•(L, I') ⟶ SheafHom^•(L', I)` of the internal Hom complexes with
sections in `Type u`. -/
theorem homMapSmall_quasiIso {I' I : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (i : I' ⟶ I) [QuasiIso i] [I'.IsKInjective] [I.IsKInjective]
    (l : L' ⟶ L) [QuasiIso l] : QuasiIso (homMapSmall X l i) := by
  have := preservesHomology_moduleULift X
  exact (Functor.FullyFaithful.quasiIso_liftCochainComplexMap_iff _ _ _ _).2
    (homMap_quasiIso X i l)

end AlgebraicGeometry.RingedSite

end
