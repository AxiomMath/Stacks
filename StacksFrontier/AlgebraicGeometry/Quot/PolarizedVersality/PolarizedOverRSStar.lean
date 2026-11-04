module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedVersality.PolarizedOverBase
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedRSStar

/-!
# Condition (RS*) for `S-𝒫olarized`

The fibre of `S-𝒫olarized` over an object `V` of the big fppf site of `S` is the fibre of
`𝒫olarized` over the underlying scheme of `V`, and the chosen pullbacks of the two agree up to
canonical isomorphism. So the comparison functor of a commutative square of the site of `S` is an
equivalence as soon as the comparison functor of `𝒫olarized` at the underlying square of schemes
is, and Stacks 0D44 (`AlgebraicGeometry.isEquivalence_polarizedPushoutRestriction`) gives condition
(RS*) of Stacks 07Y8 for `S-𝒫olarized`, as the base's
`AlgebraicGeometry.satisfiesRSStar_polarizedSliceProjection` does for `𝒫olarized` over a terminal
base. The comparison follows
`CategoryTheory.Functor.isEquivalence_fiberSquareComparison_sliceAtTerminal`.

## Main results

* `PolarizedOver.fiberFunctor`: the fibre of `S-𝒫olarized` over `V` is the fibre of `𝒫olarized`
  over `V.left`.
* `PolarizedOver.isEquivalence_fiberSquareComparison_projection`: the comparison functor of a
  square of the site of `S`, for `S-𝒫olarized`, is an equivalence as soon as that of `𝒫olarized`
  at the underlying square of schemes is.
* `PolarizedOver.satisfiesRSStar_projection`: (RS*) for `S-𝒫olarized`.

## References

* [Stacks Project, Tag 0D44](https://stacks.math.columbia.edu/tag/0D44)
* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

@[expose] public noncomputable section

namespace AlgebraicGeometry.PolarizedVersality.PolarizedOver

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The fibre of `S-𝒫olarized` over `V` is the fibre of `𝒫olarized` over `V.left`. -/
def fiberFunctor (V : BigFppfOver B S hS) :
    (projection B S hS).Fiber V ⥤ (polarizedProjection B).Fiber V.left where
  obj x := ⟨x.1.polarized, congrArg Comma.left x.2⟩
  map φ := ⟨φ.1.polarizedHom, isHomLift_polarizedProjection (𝟙 V) φ.1 φ.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The underlying object of `(fiberFunctor V).obj x` is the polarized family of `x`. -/
@[simp]
theorem fiberInclusion_obj_fiberFunctor_obj (V : BigFppfOver B S hS)
    (x : (projection B S hS).Fiber V) :
    Fiber.fiberInclusion.obj ((fiberFunctor V).obj x) = (Fiber.fiberInclusion.obj x).polarized :=
  rfl

/-- The underlying morphism of `(fiberFunctor V).map u` is the morphism of polarized families of
`u`. -/
@[simp]
theorem fiberInclusion_map_fiberFunctor_map (V : BigFppfOver B S hS)
    {x y : (projection B S hS).Fiber V} (u : x ⟶ y) :
    Fiber.fiberInclusion.map ((fiberFunctor V).map u) =
      (Fiber.fiberInclusion.map u).polarizedHom :=
  rfl

/-- The functor `fiberFunctor V` is faithful. -/
instance (V : BigFppfOver B S hS) : (fiberFunctor V).Faithful where
  map_injective {_ _} _ _ h := Subtype.ext (PolarizedFamilyOver.Hom.ext (congrArg Subtype.val h))

/-- The functor `fiberFunctor V` is full. -/
instance (V : BigFppfOver B S hS) : (fiberFunctor V).Full where
  map_surjective {x y} ψ := by
    obtain ⟨ψ, hψ⟩ := ψ
    have hfac := IsHomLift.fac' (polarizedProjection B) (𝟙 V.left) ψ
    have hb : ψ.baseMap ≫ y.1.toBase = x.1.toBase := by
      rw [toBase_eq y.2, toBase_eq x.2]
      exact comp_eqToHom_hom_eq (𝟙 V) ψ.baseMap _ _ hfac
    exact ⟨⟨homMk ψ hb, isHomLift_projection (𝟙 V) (homMk ψ hb) x.2 y.2 hψ⟩, rfl⟩

/-- The functor `fiberFunctor V` is essentially surjective. -/
instance (V : BigFppfOver B S hS) : (fiberFunctor V).EssSurj where
  mem_essImage z := ⟨⟨ofBase z.1 V z.2, projection_obj_ofBase z.1 V z.2⟩, ⟨Iso.refl _⟩⟩

/-- The functor `fiberFunctor V` is an equivalence. -/
instance (V : BigFppfOver B S hS) : (fiberFunctor V).IsEquivalence where

/-- The chosen pullbacks of `S-𝒫olarized` are cartesian in `𝒫olarized`. -/
theorem isCartesian_chosenPullbacks_map {A A' : BigFppfOver B S hS} (g : A ⟶ A')
    (y : (projection B S hS).Fiber A') :
    (polarizedProjection B).IsCartesian g.left
      ((chosenPullbacks (projection B S hS)).map g y).polarizedHom := by
  have : (polarizedProjection B).IsHomLift g.left
      ((chosenPullbacks (projection B S hS)).map g y).polarizedHom :=
    isHomLift_polarizedProjection g _ inferInstance
  exact (polarizedProjection_isFiberedInGroupoids_unconditional.isStronglyCartesian_homLift g.left
    _).isCartesian_of_isStronglyCartesian

/-- The chosen pullback in `S-𝒫olarized`, read in the fibres of `𝒫olarized`, is the chosen
pullback of `𝒫olarized`. -/
def pullbackIso {A A' : BigFppfOver B S hS} (g : A ⟶ A') :
    letI : (polarizedProjection B).IsFibered :=
      polarizedProjection_isFiberedInGroupoids_unconditional.isFibered
    (chosenPullbacks (projection B S hS)).pullbackFunctor g ⋙ fiberFunctor A ≅
      fiberFunctor A' ⋙ fiberPullback (polarizedProjection B) g.left :=
  letI : (polarizedProjection B).IsFibered :=
    polarizedProjection_isFiberedInGroupoids_unconditional.isFibered
  NatIso.ofComponents
    (fun y => fiberIsoOfCartesian g.left
      ((chosenPullbacks (projection B S hS)).map g y).polarizedHom
      (fiberPullbackHom (polarizedProjection B) g.left ((fiberFunctor A').obj y))
      (isCartesian_chosenPullbacks_map g y)
      (isCartesian_fiberPullbackHom (polarizedProjection B) g.left _))
    (fun {y y'} α => by
      refine fiber_hom_ext_of_cartesian g.left
        (fiberPullbackHom (polarizedProjection B) g.left ((fiberFunctor A').obj y'))
        (isCartesian_fiberPullbackHom (polarizedProjection B) g.left _) _ _ ?_
      have h1 := fiberIsoOfCartesian_hom_fac g.left
        (z := (fiberFunctor A).obj ((chosenPullbacks (projection B S hS)).obj g y'))
        (z' := (fiberPullback (polarizedProjection B) g.left).obj ((fiberFunctor A').obj y'))
        ((chosenPullbacks (projection B S hS)).map g y').polarizedHom
        (fiberPullbackHom (polarizedProjection B) g.left ((fiberFunctor A').obj y'))
        (isCartesian_chosenPullbacks_map g y')
        (isCartesian_fiberPullbackHom (polarizedProjection B) g.left _)
      have h2 := fiberIsoOfCartesian_hom_fac g.left
        (z := (fiberFunctor A).obj ((chosenPullbacks (projection B S hS)).obj g y))
        (z' := (fiberPullback (polarizedProjection B) g.left).obj ((fiberFunctor A').obj y))
        ((chosenPullbacks (projection B S hS)).map g y).polarizedHom
        (fiberPullbackHom (polarizedProjection B) g.left ((fiberFunctor A').obj y))
        (isCartesian_chosenPullbacks_map g y)
        (isCartesian_fiberPullbackHom (polarizedProjection B) g.left _)
      simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
      rw [fiberPullback_map_fac (polarizedProjection B) g.left ((fiberFunctor A').map α)]
      refine (congrArg (Fiber.fiberInclusion.map ((fiberFunctor A).map
        (((chosenPullbacks (projection B S hS)).pullbackFunctor g).map α)) ≫ ·) h1).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _)
      refine Eq.trans ?_ (congrArg (· ≫ Fiber.fiberInclusion.map ((fiberFunctor A').map α))
        h2.symm)
      exact congrArg PolarizedFamilyOver.Hom.polarizedHom
        ((chosenPullbacks (projection B S hS)).homMap_fac g α))

/-- The comparison of chosen pullbacks commutes with the cartesian morphisms. -/
@[reassoc (attr := simp)]
theorem pullbackIso_hom_app_fac {A A' : BigFppfOver B S hS} (g : A ⟶ A')
    (y : (projection B S hS).Fiber A') :
    letI : (polarizedProjection B).IsFibered :=
      polarizedProjection_isFiberedInGroupoids_unconditional.isFibered
    Fiber.fiberInclusion.map ((pullbackIso g).hom.app y) ≫
        fiberPullbackHom (polarizedProjection B) g.left ((fiberFunctor A').obj y) =
      ((chosenPullbacks (projection B S hS)).map g y).polarizedHom := by
  let : (polarizedProjection B).IsFibered :=
    polarizedProjection_isFiberedInGroupoids_unconditional.isFibered
  exact fiberIsoOfCartesian_hom_fac _ _ _ _ _

/-- The inverse comparison of chosen pullbacks commutes with the cartesian morphisms. -/
@[reassoc (attr := simp)]
theorem pullbackIso_inv_app_fac {A A' : BigFppfOver B S hS} (g : A ⟶ A')
    (y : (projection B S hS).Fiber A') :
    letI : (polarizedProjection B).IsFibered :=
      polarizedProjection_isFiberedInGroupoids_unconditional.isFibered
    Fiber.fiberInclusion.map ((pullbackIso g).inv.app y) ≫
        ((chosenPullbacks (projection B S hS)).map g y).polarizedHom =
      fiberPullbackHom (polarizedProjection B) g.left ((fiberFunctor A').obj y) := by
  let : (polarizedProjection B).IsFibered :=
    polarizedProjection_isFiberedInGroupoids_unconditional.isFibered
  exact fiberIsoOfCartesian_inv_fac _ _ _ _ _

/-- `choiceOfPullbacks_pullbackFunctorCompIso_hom_app_fac`, read on polarized families. -/
@[reassoc (attr := simp)]
theorem polarizedHom_pullbackFunctorCompIso_hom_app_fac
    (c : (projection B S hS).ChoiceOfPullbacks) {W V U : BigFppfOver B S hS} (g : W ⟶ V)
    (f : V ⟶ U) (x : (projection B S hS).Fiber U) :
    (Fiber.fiberInclusion.map ((c.pullbackFunctorCompIso g f).hom.app x)).polarizedHom ≫
        (c.map g (c.obj f x)).polarizedHom ≫ (c.map f x).polarizedHom =
      (c.map (g ≫ f) x).polarizedHom :=
  congrArg PolarizedFamilyOver.Hom.polarizedHom
    (choiceOfPullbacks_pullbackFunctorCompIso_hom_app_fac c g f x)

/-- `choiceOfPullbacks_pullbackFunctorCompIso_inv_app_fac`, read on polarized families. -/
@[reassoc (attr := simp)]
theorem polarizedHom_pullbackFunctorCompIso_inv_app_fac
    (c : (projection B S hS).ChoiceOfPullbacks) {W V U : BigFppfOver B S hS} (g : W ⟶ V)
    (f : V ⟶ U) (x : (projection B S hS).Fiber U) :
    (Fiber.fiberInclusion.map ((c.pullbackFunctorCompIso g f).inv.app x)).polarizedHom ≫
        (c.map (g ≫ f) x).polarizedHom =
      (c.map g (c.obj f x)).polarizedHom ≫ (c.map f x).polarizedHom :=
  congrArg PolarizedFamilyOver.Hom.polarizedHom
    (choiceOfPullbacks_pullbackFunctorCompIso_inv_app_fac c g f x)

/-- `eqToHom_app_choiceOfPullbacks_map`, read on polarized families. -/
@[reassoc (attr := simp)]
theorem polarizedHom_eqToHom_app_choiceOfPullbacks_map
    (c : (projection B S hS).ChoiceOfPullbacks) {U V : BigFppfOver B S hS} {g g' : U ⟶ V}
    (h : g = g') (x : (projection B S hS).Fiber V) :
    (Fiber.fiberInclusion.map ((eqToIso (congrArg c.pullbackFunctor h)).hom.app x)).polarizedHom ≫
        (c.map g' x).polarizedHom = (c.map g x).polarizedHom :=
  congrArg PolarizedFamilyOver.Hom.polarizedHom (eqToHom_app_choiceOfPullbacks_map c h x)

section Square

variable {X X' Y Y' : BigFppfOver B S hS} (i : X ⟶ X') (f : X ⟶ Y) (a : X' ⟶ Y') (b : Y ⟶ Y')
  (w : i ≫ a = f ≫ b)

attribute [local implicit_reducible] CategoryTheory.Functor.fiberSquareRestriction
  CategoryTheory.Limits.CategoricalPullback.map
  CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
  AlgebraicGeometry.PolarizedVersality.PolarizedOver.fiberFunctor
  CategoryTheory.Functor.fiberPullback
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor

/-- The coherence of the comparison of the two fibre squares, in explicit form. -/
theorem square_coherence (z : (projection B S hS).Fiber Y') :
    letI : (polarizedProjection B).IsFibered :=
      polarizedProjection_isFiberedInGroupoids_unconditional.isFibered
    (fiberPullback (polarizedProjection B) f.left).map ((pullbackIso b).hom.app z) ≫
        (fiberPullbackSquareIso (polarizedProjection B) i.left f.left a.left b.left
          (left_comm_of_comm i f a b w)).hom.app ((fiberFunctor Y').obj z) =
      ((pullbackIso f).inv.app ((chosenPullbacks (projection B S hS)).obj b z) ≫
        (fiberFunctor X).map
          ((((chosenPullbacks (projection B S hS)).pullbackFunctorCompIso f b).symm ≪≫
            eqToIso (congrArg (chosenPullbacks (projection B S hS)).pullbackFunctor w.symm) ≪≫
            (chosenPullbacks (projection B S hS)).pullbackFunctorCompIso i a).hom.app z) ≫
        (pullbackIso i).hom.app ((chosenPullbacks (projection B S hS)).obj a z)) ≫
        (fiberPullback (polarizedProjection B) i.left).map ((pullbackIso a).hom.app z) := by
  let : (polarizedProjection B).IsFibered :=
    polarizedProjection_isFiberedInGroupoids_unconditional.isFibered
  refine fiber_hom_ext_of_cartesian (i.left ≫ a.left)
    (fiberPullbackHom (polarizedProjection B) i.left
      ((fiberPullback (polarizedProjection B) a.left).obj ((fiberFunctor Y').obj z)) ≫
      fiberPullbackHom (polarizedProjection B) a.left ((fiberFunctor Y').obj z))
    (isCartesian_fiberPullbackHom_comp (polarizedProjection B) i.left a.left _) _ _ ?_
  simp only [fiberPullbackSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc, Functor.comp_obj, fiberPullbackCompIso_inv_app_fac,
    fiberPullback_map_fac_assoc, pullbackIso_hom_app_fac, pullbackIso_hom_app_fac_assoc,
    fiberInclusion_map_fiberFunctor_map, polarizedHom_pullbackFunctorCompIso_hom_app_fac]
  rw [polarizedHom_eqToHom_app_choiceOfPullbacks_map _ w.symm,
    eqToHom_app_fiberPullbackHom (polarizedProjection B) (left_comm_of_comm i f a b w)]
  simp only [fiberPullbackCompIso_hom_app_fac, fiberPullback_map_fac_assoc,
    pullbackIso_hom_app_fac, polarizedHom_pullbackFunctorCompIso_inv_app_fac]
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ ((chosenPullbacks (projection B S hS)).map b z).polarizedHom)
      (pullbackIso_inv_app_fac f _))).symm

/-- **The comparison functor of a square of the site of `S`, for `S-𝒫olarized`, is an
equivalence as soon as the comparison functor of `𝒫olarized` at the underlying square of
schemes is.** -/
theorem isEquivalence_fiberSquareComparison_projection
    (h : letI : (polarizedProjection B).IsFibered :=
        polarizedProjection_isFiberedInGroupoids_unconditional.isFibered
      (fiberSquareRestriction (polarizedProjection B) i.left f.left a.left b.left
        (left_comm_of_comm i f a b w)).IsEquivalence) :
    (Deformation.Artin.fiberSquareComparison (projection B S hS)
      (chosenPullbacks (projection B S hS)) f i b a w.symm).IsEquivalence := by
  let : (polarizedProjection B).IsFibered :=
    polarizedProjection_isFiberedInGroupoids_unconditional.isFibered
  let Φ := CategoricalPullback.map ((chosenPullbacks (projection B S hS)).pullbackFunctor f)
    ((chosenPullbacks (projection B S hS)).pullbackFunctor i) (fiberFunctor Y)
    (fiberFunctor X') (fiberFunctor X) (fiberPullback (polarizedProjection B) f.left)
    (fiberPullback (polarizedProjection B) i.left) (pullbackIso i).symm (pullbackIso f)
  have : Φ.IsEquivalence :=
    induced_isEquivalence_of_isEquivalence (fiberFunctor Y) (fiberFunctor X')
      (fiberFunctor X) _ _
  let θ : Deformation.Artin.fiberSquareComparison (projection B S hS)
      (chosenPullbacks (projection B S hS)) f i b a w.symm ⋙ Φ ≅
      fiberFunctor Y' ⋙ fiberSquareRestriction (polarizedProjection B) i.left f.left a.left
        b.left (left_comm_of_comm i f a b w) :=
    NatIso.ofComponents
      (fun z => CategoricalPullback.mkIso ((pullbackIso b).app z)
        ((pullbackIso a).app z) (square_coherence i f a b w z))
      (fun {z z'} φ => CategoricalPullback.hom_ext
        ((pullbackIso b).hom.naturality φ) ((pullbackIso a).hom.naturality φ))
  have : (fiberFunctor Y' ⋙ fiberSquareRestriction (polarizedProjection B) i.left f.left a.left
      b.left (left_comm_of_comm i f a b w)).IsEquivalence := inferInstance
  have := Functor.isEquivalence_of_iso θ.symm
  exact Functor.isEquivalence_of_comp_right _ Φ

end Square

variable (B S hS) in
/-- **`S-𝒫olarized` satisfies condition (RS*)** (Stacks 07Y8), by Stacks 0D44. -/
theorem satisfiesRSStar_projection :
    Deformation.Artin.SatisfiesRSStar B S hS (projection B S hS)
      (isFiberedInGroupoids_projection B S hS) := by
  refine Deformation.Artin.satisfiesRSStar_of_fiberSquareComparison_isEquivalence_of_isAffine
    B S hS _ _ fun {X X' Y Y'} i f a b w hX hX' hY hY' hfirst hpush => ?_
  have : IsAffine (B.inclusion.obj X.left) := hX
  have : IsAffine (B.inclusion.obj Y.left) := hY
  exact isEquivalence_fiberSquareComparison_projection i f a b w
    (isEquivalence_polarizedPushoutRestriction B i.left f.left a.left b.left
      (left_comm_of_comm i f a b w) hpush.flip hfirst.isThickening)

end AlgebraicGeometry.PolarizedVersality.PolarizedOver

end
