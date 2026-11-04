module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankChartSectionsConverse
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreePowers
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteLocallyFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSheafStalkBasis
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentGenericFreeChart

/-!
# Free modules on the slice of the small étale site at an affine chart

Let `F` be an algebraic space and `T` an étale scheme chart of `F` whose scheme is affine.  This
file collects the criteria for the restriction `M|_T` of an `𝒪_F`-module to the slice site at
`T` to be free of finite rank, read on the sections over `T`.

## Main results

* `AlgebraicGeometry.Space.nonempty_iso_free_over_of_basis`: if `M` is cartesian on affine charts
  and its sections over `T` are free on a finite basis, then `M|_T` is free on the same index.
* `AlgebraicGeometry.Space.nonempty_basis_of_iso_free_over`: conversely an isomorphism of `M|_T`
  with a finite free module gives a basis of the sections over every chart above `T`.
* `AlgebraicGeometry.Space.isIso_over_map_of_bijective_app`: a morphism `M ⟶ N` with `M|_T`
  finite free and `N` cartesian on affine charts which is bijective on the sections over `T`
  becomes an isomorphism on the slice at `T`.
* `AlgebraicGeometry.Space.nonempty_iso_free_symmetricPower_over`: the symmetric powers of a
  module whose restriction to `T` is free on `γ` are free on the slice at `T`, on the monomials
  of the degree in `γ`.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_of_coversTop_iso_free`: a module which is
  finite free on the members of a covering family is finite locally free.

## Implementation notes

The isomorphism criterion uses the comparison morphism attached to a family of sections over
`T`, assembled from the sections of `G|_T` restricting that family; the restriction of a basis
along a morphism of affine charts is `AlgebraicGeometry.Space.exists_basis_restrict`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u u₁ v₁

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### The comparison morphism attached to a basis -/

/-- The morphism from a coproduct of copies of the structure sheaf on the slice at `U`
determined by a family of sections of `G` over `U`: its `i`-th component is the global section
of `G|_U` whose value over a chart above `U` is the restriction of `t i`. -/
private noncomputable def sliceFreeComparison (G : Modules.{u, u} B S hS F hF)
    (U : SmallEtale B S hS F) {I : Type u} (t : I → G.val.obj (op U)) :
    SheafOfModules.free (R := SmallEtale.sliceRingSheaf B S hS F hF U) I ⟶
      SmallEtale.sliceModule B S hS F hF U G :=
  (SheafOfModules.freeHomEquiv _).symm fun i =>
    PresheafOfModules.sectionsMk (fun V => G.val.map V.unop.hom.op (t i)) (by
      intro V W g
      exact (PresheafOfModules.map_comp_apply (M := G.val) (unop V).hom.op
          (Over.Hom.left g.unop).op (t i)).symm.trans
        (congrArg (fun k : (unop W).left ⟶ U => G.val.map k.op (t i)) (Over.w g.unop)))

private theorem sliceFreeComparison_app_single (G : Modules.{u, u} B S hS F hF)
    (U : SmallEtale B S hS F) {I : Type u} (t : I → G.val.obj (op U)) (V : Over U) (i : I)
    (a : chartRing B S hS F hF V.left) :
    ((sliceFreeComparison B S hS F hF G U t).val.app (op V)).hom
        ((Stacks.Sites.freeSectionsMap
          (R := SmallEtale.sliceRingSheaf B S hS F hF U) I (op V)).hom
            (Finsupp.single i a)) =
      a • chartRestrictLinear G V.hom (t i) :=
  Stacks.SheafOfModules.freeHomEquiv_symm_val_app_freeSectionsMap_single
    (SmallEtale.sliceModule B S hS F hF U G) _ (op V) i a

/-- **The comparison morphism attached to a basis is bijective on the sections over an affine
chart below.** -/
private theorem bijective_sliceFreeComparison_app (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G) (U : SmallEtale B S hS F)
    (hU : IsAffine (chartScheme U)) {I : Type u}
    (b : Module.Basis I (chartRing B S hS F hF U) (G.val.obj (op U)))
    (V : Over U) (hV : IsAffine (chartScheme V.left)) :
    Function.Bijective
      ((sliceFreeComparison B S hS F hF G U (fun i => b i)).val.app (op V)).hom := by
  classical
  have hfs : Function.Bijective (Stacks.Sites.freeSectionsMap
      (R := SmallEtale.sliceRingSheaf B S hS F hF U) I (op V)).hom :=
    Stacks.Sites.bijective_freeSectionsMap I V
      (GrothendieckTopology.isQuasiCompactObject_over _ V
        (isQuasiCompactObject_of_isAffine B S hS F V.left hV))
  obtain ⟨b'', hb''⟩ := exists_basis_restrict G hG hU hV V.hom b
  let b' : Module.Basis I ((SmallEtale.sliceRingSheaf B S hS F hF U).obj.obj (op V))
      ((SmallEtale.sliceModule B S hS F hF U G).val.obj (op V)) := b''
  have hsingle : ∀ (i : I) (a : (SmallEtale.sliceRingSheaf B S hS F hF U).obj.obj (op V)),
      ((sliceFreeComparison B S hS F hF G U (fun i => b i)).val.app (op V)).hom
          ((Stacks.Sites.freeSectionsMap
            (R := SmallEtale.sliceRingSheaf B S hS F hF U) I (op V)).hom
              (Finsupp.single i a)) = b'.repr.symm (Finsupp.single i a) := by
    intro i a
    have hbi : b' i = chartRestrictLinear G V.hom (b i) := hb'' i
    have h2 : b'.repr.symm (Finsupp.single i a) = a • b' i :=
      Module.Basis.repr_symm_single b' i a
    refine (sliceFreeComparison_app_single B S hS F hF G U (fun i => b i) V i a).trans ?_
    rw [h2, hbi]
    rfl
  have hAM : (((sliceFreeComparison B S hS F hF G U (fun i => b i)).val.app
        (op V)).hom.toAddMonoidHom.comp
      (Stacks.Sites.freeSectionsMap
        (R := SmallEtale.sliceRingSheaf B S hS F hF U) I (op V)).hom.toAddMonoidHom) =
      (b'.repr.symm : (I →₀ (SmallEtale.sliceRingSheaf B S hS F hF U).obj.obj (op V))
        →ₗ[_] _).toAddMonoidHom :=
    Finsupp.addHom_ext (by intro i a; exact hsingle i a)
  have hcomp : (fun p => ((sliceFreeComparison B S hS F hF G U (fun i => b i)).val.app
        (op V)).hom ((Stacks.Sites.freeSectionsMap
          (R := SmallEtale.sliceRingSheaf B S hS F hF U) I (op V)).hom p)) =
      fun p => b'.repr.symm p := by
    funext p
    simpa only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
      LinearEquiv.coe_coe] using DFunLike.congr_fun hAM p
  have hbij : Function.Bijective
      (fun p => ((sliceFreeComparison B S hS F hF G U (fun i => b i)).val.app (op V)).hom
        ((Stacks.Sites.freeSectionsMap
          (R := SmallEtale.sliceRingSheaf B S hS F hF U) I (op V)).hom p)) := by
    rw [hcomp]
    exact b'.repr.symm.bijective
  exact (Function.Bijective.of_comp_iff _ hfs).1 hbij


include hF in
/-- The comparison morphism attached to a basis of the sections over an affine chart is an
isomorphism, for a module cartesian on affine charts. -/
private theorem isIso_sliceFreeComparison (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G) (U : SmallEtale B S hS F)
    (hU : IsAffine (chartScheme U)) {I : Type u}
    (b : Module.Basis I (chartRing B S hS F hF U) (G.val.obj (op U))) :
    IsIso (sliceFreeComparison B S hS F hF G U (fun i => b i)) :=
  SmallEtale.isIso_of_bijective_app_of_isAffine B S hS F hF U _ fun V hV =>
    bijective_sliceFreeComparison_app B S hS F hF G hG U hU b V hV

/-! ### Free on the slice from a basis of the sections -/

/-- **A module cartesian on affine charts whose sections over an affine chart `T` are free is
free on the slice at `T`**, on the same index type. -/
theorem nonempty_iso_free_over_of_basis (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G) (T : SmallEtale B S hS F)
    (hT : IsAffine (chartScheme T)) {I : Type u}
    (b : Module.Basis I (chartRing B S hS F hF T) (G.val.obj (op T))) :
    Nonempty (G.over T ≅ SheafOfModules.free (R := SmallEtale.sliceRingSheaf B S hS F hF T) I) :=
  have := isIso_sliceFreeComparison B S hS F hF G hG T hT b
  ⟨(asIso (sliceFreeComparison B S hS F hF G T (fun i => b i))).symm⟩

/-! ### A basis of the sections from a free restriction -/

/-- The basis of the sections over an affine chart `V` above `T` of a module whose restriction to
the slice at `T` is identified with a free module: the image of the standard basis of the
sections of the free module. -/
noncomputable def basisOfIsoFreeOver (G : Modules.{u, u} B S hS F hF) (T : SmallEtale B S hS F)
    {I : Type u}
    (e : G.over T ≅ SheafOfModules.free (R := SmallEtale.sliceRingSheaf B S hS F hF T) I)
    (V : Over T) (hV : IsAffine (chartScheme V.left)) :
    Module.Basis I ((SmallEtale.sliceRingSheaf B S hS F hF T).obj.obj (op V))
      ((SmallEtale.sliceModule B S hS F hF T G).val.obj (op V)) :=
  (Finsupp.basisSingleOne (ι := I)
      (R := (SmallEtale.sliceRingSheaf B S hS F hF T).obj.obj (op V))).map
    ((LinearEquiv.ofBijective (Stacks.Sites.freeSectionsMap
        (R := SmallEtale.sliceRingSheaf B S hS F hF T) I (op V)).hom
      (Stacks.Sites.bijective_freeSectionsMap I V
        (GrothendieckTopology.isQuasiCompactObject_over _ V
          (isQuasiCompactObject_of_isAffine B S hS F V.left hV)))).trans
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ (op V)).mapIso
        e.symm).toLinearEquiv)

/-- The elements of `AlgebraicGeometry.Space.basisOfIsoFreeOver` are the values of the images of
the tautological sections of the free module. -/
theorem basisOfIsoFreeOver_apply (G : Modules.{u, u} B S hS F hF) (T : SmallEtale B S hS F)
    {I : Type u}
    (e : G.over T ≅ SheafOfModules.free (R := SmallEtale.sliceRingSheaf B S hS F hF T) I)
    (V : Over T) (hV : IsAffine (chartScheme V.left)) (i : I) :
    basisOfIsoFreeOver B S hS F hF G T e V hV i =
      PresheafOfModules.sections.eval
        (SheafOfModules.sectionsMap e.inv (SheafOfModules.freeSection i)) (op V) := by
  have h := Stacks.SheafOfModules.freeHomEquiv_symm_val_app_freeSectionsMap_single
    (SheafOfModules.free (R := SmallEtale.sliceRingSheaf B S hS F hF T) I)
    (fun j => SheafOfModules.freeSection j) (op V) i 1
  rw [one_smul, show (fun j => SheafOfModules.freeSection j) =
      (SheafOfModules.free (R := SmallEtale.sliceRingSheaf B S hS F hF T) I).freeHomEquiv
        (𝟙 _) from rfl, Equiv.symm_apply_apply] at h
  simp only [basisOfIsoFreeOver, Module.Basis.map_apply, Finsupp.coe_basisSingleOne]
  exact congrArg (fun x => ((SheafOfModules.forget (SmallEtale.sliceRingSheaf B S hS F hF T) ⋙
    PresheafOfModules.evaluation (SmallEtale.sliceRingSheaf B S hS F hF T).obj (op V)).map
      e.inv).hom x) h

/-- **An isomorphism of the restriction to the slice at `T` with a free module gives a basis of
the sections over every affine chart above `T`.** -/
theorem nonempty_basis_of_iso_free_over (G : Modules.{u, u} B S hS F hF) (T : SmallEtale B S hS F)
    {I : Type u}
    (e : G.over T ≅ SheafOfModules.free (R := SmallEtale.sliceRingSheaf B S hS F hF T) I)
    (V : Over T) (hV : IsAffine (chartScheme V.left)) :
    Nonempty (Module.Basis I ((SmallEtale.sliceRingSheaf B S hS F hF T).obj.obj (op V))
      ((SmallEtale.sliceModule B S hS F hF T G).val.obj (op V))) :=
  ⟨basisOfIsoFreeOver B S hS F hF G T e V hV⟩

/-! ### An isomorphism criterion on the slice -/

include hF in
/-- **A morphism out of a module which is free on the slice at an affine chart `T`, into a module
cartesian on affine charts, becomes an isomorphism on the slice at `T` as soon as it is bijective
on the sections over `T`.** -/
theorem isIso_over_map_of_bijective_app {M N : Modules.{u, u} B S hS F hF} (φ : M ⟶ N)
    (hN : IsCartesianOnAffineCharts N) (T : SmallEtale B S hS F)
    (hT : IsAffine (chartScheme T)) {I : Type u}
    (e : M.over T ≅ SheafOfModules.free (R := SmallEtale.sliceRingSheaf B S hS F hF T) I)
    (hφ : Function.Bijective (φ.val.app (op T)).hom) :
    IsIso ((SheafOfModules.overFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) T).map φ) := by
  let t : Over T := Over.mk (𝟙 T)
  let b0 : Module.Basis I (chartRing B S hS F hF T) (M.val.obj (op T)) :=
    basisOfIsoFreeOver B S hS F hF M T e t hT
  let L : M.val.obj (op T) ≃ₗ[chartRing B S hS F hF T] N.val.obj (op T) :=
    LinearEquiv.ofBijective (φ.val.app (op T)).hom hφ
  let b' : Module.Basis I (chartRing B S hS F hF T) (N.val.obj (op T)) := b0.map L
  have := isIso_sliceFreeComparison B S hS F hF N hN T hT b'
  have heq : e.inv ≫ φ.over T = sliceFreeComparison B S hS F hF N T (fun i => b' i) := by
    refine (SheafOfModules.freeHomEquiv _).injective (funext fun i => ?_)
    refine (SheafOfModules.freeHomEquiv_comp_apply e.inv (φ.over T) i).trans ?_
    refine Eq.trans ?_ (congrFun ((SheafOfModules.freeHomEquiv _).apply_symm_apply _) i).symm
    refine PresheafOfModules.sections_ext _ _ fun X => ?_
    have hb : b' i = (φ.val.app (op T)).hom
        (PresheafOfModules.sections.eval
          (SheafOfModules.sectionsMap e.inv (SheafOfModules.freeSection i)) (op t)) :=
      congrArg L (basisOfIsoFreeOver_apply B S hS F hF M T e t hT i)
    have hs := PresheafOfModules.sections_property
      (SheafOfModules.sectionsMap e.inv (SheafOfModules.freeSection i))
      (Over.homMk X.unop.hom (Category.comp_id _) : X.unop ⟶ t).op
    show (φ.val.app (op X.unop.left)).hom
        ((SheafOfModules.sectionsMap e.inv (SheafOfModules.freeSection i)).val X) =
      N.val.map X.unop.hom.op (b' i)
    rw [hb, ← hs]
    exact (PresheafOfModules.naturality_apply φ.val X.unop.hom.op
      (PresheafOfModules.sections.eval
        (SheafOfModules.sectionsMap e.inv (SheafOfModules.freeSection i)) (op t)))
  have hcomp : IsIso (e.inv ≫ φ.over T) := heq ▸ this
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ e.inv (φ.over T) (Iso.isIso_inv e) hcomp

/-! ### Symmetric powers of a module free on the slice -/

/-- The tensor, exterior and symmetric algebras of a module on the small étale site. -/
private noncomputable def symmetricAlgebras (Cm : Modules.{u, u} B S hS F hF) :
    SheafOfModules.TensorExteriorSymmetricAlgebras.{u, u + 1, u}
      (smallEtaleRingedSite B S hS F hF).J Cm :=
  have h1 : (smallEtaleRingedSite B S hS F hF).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    SmallEtale.instWEqualsLocallyBijective B S hS F AddCommGrpCat.{u}
  have h2 : HasWeakSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{u} :=
    smallEtaleRingedSite_hasWeakSheafify_addCommGrpCat B S hS F hF
  have h3 : (smallEtaleRingedSite B S hS F hF).J.HasSheafCompose
      (forget₂ CommRingCat.{u} RingCat.{u}) :=
    (smallEtaleRingedSite B S hS F hF).hasSheafCompose_forget₂_ringCat
  @SheafOfModules.algebras.{u, u + 1, u} _ _ (smallEtaleRingedSite B S hS F hF).J h3
    (smallEtaleRingedSite B S hS F hF).O h1 h2 Cm

/-- **The symmetric powers of a module whose restriction to the slice at `T` is free on `γ` are
free on the slice at `T`, on the monomials of the degree in `γ`.**  Here the symmetric powers are
the homogeneous pieces of an arbitrary symmetric algebra `A` of the module on the small étale
site. -/
theorem nonempty_iso_free_symmetricPower_over (Cm : Modules.{u, u} B S hS F hF)
    (A : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
    (ι : Cm ⟶ A.piece 1) (hA : SheafOfModules.GradedAlgebra.IsSymmetricAlgebra A ι)
    (T : SmallEtale B S hS F) {γ : Type u} [DecidableEq γ]
    (e : Cm.over T ≅ SheafOfModules.free (R := SmallEtale.sliceRingSheaf B S hS F hF T) γ)
    (n : ℕ) :
    Nonempty ((A.piece (n : ℤ)).over T ≅
      SheafOfModules.free (R := SmallEtale.sliceRingSheaf B S hS F hF T)
        {d : γ →₀ ℕ | d.degree = n}) := by
  have h4 : ∀ U : (smallEtaleRingedSite B S hS F hF).C,
      ((smallEtaleRingedSite B S hS F hF).J.over U).HasSheafCompose
        (forget₂ CommRingCat.{u} RingCat.{u}) := fun U =>
    ((smallEtaleRingedSite B S hS F hF).over U).hasSheafCompose_forget₂_ringCat
  have h5 := smallEtaleRingedSite_hasWeakSheafify_over B S hS F hF
  have h6 := smallEtaleRingedSite_wEqualsLocallyBijective_over B S hS F hF
  let P := symmetricAlgebras B S hS F hF Cm
  exact ⟨((SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) T).mapIso
      (hA.pieceIso P.symmetric_isSymmetricAlgebra (n : ℤ))).trans
    (Stacks.SheafOfModules.symmetricPowerOverFreeIsoOfIsoFree P T n γ e)⟩

/-- **A symmetric algebra of a module on the small étale site vanishes in negative degrees.** -/
theorem isZero_piece_of_isSymmetricAlgebra_of_neg (Cm : Modules.{u, u} B S hS F hF)
    (A : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
    (ι : Cm ⟶ A.piece 1) (hA : SheafOfModules.GradedAlgebra.IsSymmetricAlgebra A ι)
    {n : ℤ} (hn : n < 0) : Limits.IsZero (A.piece n) := by
  let P := symmetricAlgebras B S hS F hF Cm
  exact (Stacks.SheafOfModules.isZero_symmetricPiece_of_neg P hn).of_iso
    (hA.pieceIso P.symmetric_isSymmetricAlgebra n)

/-! ### Finite local freeness from a covering family -/

/-- A module isomorphic to a free module on a finite index type is finite free. -/
theorem isFiniteFree_of_iso_free {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {R : Sheaf J RingCat.{u}} {M : SheafOfModules.{u} R} {γ : Type u} [Finite γ]
    (e : M ≅ SheafOfModules.free (R := R) γ) : SheafOfModules.IsFiniteFree R M := by
  obtain ⟨ι, ⟨hc⟩⟩ := Stacks.SheafOfModules.exists_isColimitCofan_of_iso_free e.symm
  exact (SheafOfModules.isFiniteFree_iff_exists_isColimit R M).2
    ⟨Nat.card γ, _, ⟨Cofan.isColimitEquivOfEquiv (Finite.equivFin γ).symm _ hc⟩⟩

/-- A finite free module is finite locally free. -/
theorem isFiniteLocallyFreeOnSite_of_isFiniteFree {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {M : SheafOfModules.{u} R}
    (h : SheafOfModules.IsFiniteFree R M) : SheafOfModules.IsFiniteLocallyFreeOnSite M := by
  intro U
  refine ⟨PUnit, fun _ => U, fun _ => 𝟙 U, ?_, fun _ =>
    Stacks.SheafOfModules.isFiniteFree_over M U h⟩
  refine J.superset_covering (fun W g _ => ?_) (J.top_mem U)
  exact (Sieve.mem_ofArrows_iff _ _ _).2 ⟨PUnit.unit, g, (Category.comp_id g).symm⟩

/-- **A module whose restrictions to the members of a family covering the final object are
finite free is finite locally free.** -/
theorem isFiniteLocallyFreeOnSite_of_coversTop_iso_free (M : Modules.{u, u} B S hS F hF)
    {I : Type (u + 1)} (T : I → SmallEtale B S hS F)
    (hT : (SmallEtale.topology B S hS F).CoversTop T) (γ : I → Type u) [∀ i, Finite (γ i)]
    (e : ∀ i, M.over (T i) ≅
      SheafOfModules.free (R := SmallEtale.sliceRingSheaf B S hS F hF (T i)) (γ i)) :
    SheafOfModules.IsFiniteLocallyFreeOnSite M :=
  (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteLocallyFreeOnSite
    (smallEtaleRingedSite B S hS F hF) M).2
    ⟨I, T, hT, fun i =>
      have : HasWeakSheafify ((smallEtaleRingedSite B S hS F hF).over (T i)).J
          AddCommGrpCat.{u} :=
        smallEtaleRingedSite_hasWeakSheafify_over B S hS F hF (T i)
      have : ((smallEtaleRingedSite B S hS F hF).over (T i)).J.WEqualsLocallyBijective
          AddCommGrpCat.{u} :=
        smallEtaleRingedSite_wEqualsLocallyBijective_over B S hS F hF (T i)
      isFiniteLocallyFreeOnSite_of_isFiniteFree (isFiniteFree_of_iso_free (γ := γ i) (e i))⟩

end AlgebraicGeometry.Space

end
