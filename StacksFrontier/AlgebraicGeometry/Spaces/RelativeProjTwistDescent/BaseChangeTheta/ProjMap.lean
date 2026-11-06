module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.RelativeProjCongrFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.FunctorialityTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.Modules
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PresentationPullbackDescent

/-!
# The fibre map of a comparison of restriction data, and morphisms lying over `h`

For a comparison of restriction data along a morphism `g` of the base, the morphism
`Proj_T(f'^*𝒜') ⟶ Proj_T((g f')^*𝒜)` over `T` (`GradedAlgebraRestriction.ComapHom.projMap`) and
its description on schemes; the notion `RelativeProjPoints.LiesOverAlong` of a morphism of base
changes of two relative Projs lying over a morphism of test objects and over a morphism `h` of the
Projs, and the induced morphism of presentations.
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist
open Stacks.AlgebraicGeometry (Tag07ZGTwist.twistAlgebra GluedTwistAlgebra.twistDataOfGradedAlgebra)

namespace AlgebraicGeometry.Space

/-! ### The fibre map of a comparison of restriction data -/

namespace GradedAlgebraRestriction

namespace ComapHom

section Fibre

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {r : GradedAlgebraPoints B S hS X} {r' : GradedAlgebraPoints B S hS X'}
    {ρ' : GradedAlgebraRestriction r'} {ρ : GradedAlgebraRestriction r} {g : X' ⟶ X}
    (e : ComapHom ρ' ρ g)

/-- **The comparison with the scheme-level functor of quadruples commutes with the bijection of
the fibres**: comparing, over `g ∘ f'`, the image of a class of `ρ'` is transporting along the
inverse of the comparison of the algebras the class compared over `f'`. -/
theorem algebraTransport_fibreToF_fibreInv {Z W : BigFppfOver B S hS} (f' : yoneda.obj Z ⟶ X')
    (t : W ⟶ Z) (f₂ : yoneda.obj W ⟶ X') (hf : yoneda.map t ≫ f' = f₂)
    (h : yoneda.map t ≫ f' ≫ g = f₂ ≫ g)
    (q : Quot (UnionRel (f := 𝟙 ((BigFppfOver.toScheme B S hS).obj W)) (A := r'.algebra W f₂))) :
    F.algebraTransport (e.hom f') (e.isIso_hom_app f')
        (ρ.fibreToF (f' ≫ g) t (f₂ ≫ g) h (e.fibreInv f₂ q)) =
      ρ'.fibreToF f' t f₂ hf q := by
  have hi₁ : ∀ n : ℤ, IsIso (((ρ'.restrict t f' f₂ hf).comp
      (baseAlgebraMapHom ((BigFppfOver.toScheme B S hS).map t) (e.hom f'))).app n) := fun n => by
    simp only [SheafOfModules.GradedAlgebra.UnitalHom.comp_app]
    infer_instance
  have hi₂ : ∀ n : ℤ, IsIso (((e.hom f₂).comp (ρ.restrict t (f' ≫ g) (f₂ ≫ g) h)).app n) :=
    fun n => by
      simp only [SheafOfModules.GradedAlgebra.UnitalHom.comp_app]
      infer_instance
  have h3 := (F.algebraTransportEquiv (ρ.restrict t (f' ≫ g) (f₂ ≫ g) h)
    (ρ.isIso_restrict_app t (f' ≫ g) (f₂ ≫ g) h) _).apply_symm_apply
      (⟨𝟙 _, e.fibreInv f₂ q⟩ : F (r.algebra W (f₂ ≫ g)) ((BigFppfOver.toScheme B S hS).obj W))
  have key : F.algebraTransport (baseAlgebraMapHom ((BigFppfOver.toScheme B S hS).map t) (e.hom f'))
      (fun n => have := e.isIso_hom_app f' n; inferInstance)
      ((F.algebraTransportEquiv (ρ.restrict t (f' ≫ g) (f₂ ≫ g) h)
        (ρ.isIso_restrict_app t (f' ≫ g) (f₂ ≫ g) h) _).symm ⟨𝟙 _, e.fibreInv f₂ q⟩) =
      (F.algebraTransportEquiv (ρ'.restrict t f' f₂ hf) (ρ'.isIso_restrict_app t f' f₂ hf) _).symm
        ⟨𝟙 _, q⟩ := by
    refine (F.algebraTransportEquiv (ρ'.restrict t f' f₂ hf)
      (ρ'.isIso_restrict_app t f' f₂ hf) _).injective (Eq.trans ?_
        ((F.algebraTransportEquiv (ρ'.restrict t f' f₂ hf)
          (ρ'.isIso_restrict_app t f' f₂ hf) _).apply_symm_apply _).symm)
    refine (F.algebraTransport_algebraTransport _ _ _ _ hi₁ _).trans ?_
    refine (F.algebraTransport_congr (e.restrict_comp_hom t f' f₂ hf h) hi₁ hi₂ _).trans ?_
    refine (F.algebraTransport_algebraTransport (e.hom f₂) (ρ.restrict t (f' ≫ g) (f₂ ≫ g) h)
      (e.isIso_hom_app f₂) (fun n => inferInstance) hi₂ _).symm.trans ?_
    refine (congrArg (F.algebraTransport (e.hom f₂) (e.isIso_hom_app f₂)) h3).trans ?_
    exact congrArg (fun z => (⟨𝟙 _, z⟩ : F (r'.algebra W f₂) ((BigFppfOver.toScheme B S hS).obj W)))
      (e.fibreMap_fibreInv f₂ q)
  unfold fibreToF
  rw [← F.baseChangeUp_algebraTransport ((BigFppfOver.toScheme B S hS).map t) (e.hom f')
    (e.isIso_hom_app f')]
  exact congrArg (F.baseChangeUp ((BigFppfOver.toScheme B S hS).map t) (r'.algebra Z f')) key

/-- `AlgebraicGeometry.Space.GradedAlgebraRestriction.ComapHom.algebraTransport_fibreToF_fibreInv`,
solved for the comparison over `g ∘ f'`. -/
theorem fibreToF_fibreInv {Z W : BigFppfOver B S hS} (f' : yoneda.obj Z ⟶ X')
    (t : W ⟶ Z) (f₂ : yoneda.obj W ⟶ X') (hf : yoneda.map t ≫ f' = f₂)
    (h : yoneda.map t ≫ f' ≫ g = f₂ ≫ g)
    (q : Quot (UnionRel (f := 𝟙 ((BigFppfOver.toScheme B S hS).obj W)) (A := r'.algebra W f₂))) :
    ρ.fibreToF (f' ≫ g) t (f₂ ≫ g) h (e.fibreInv f₂ q) =
      F.algebraTransport (unitalHomInverse (e.hom f') (e.isIso_hom_app f'))
        (isIso_unitalHomInverse_app _ _) (ρ'.fibreToF f' t f₂ hf q) := by
  rw [← e.algebraTransport_fibreToF_fibreInv f' t f₂ hf h q]
  exact ((F.algebraTransportEquiv (e.hom f') (e.isIso_hom_app f') _).symm_apply_apply _).symm

end Fibre

section ProjMap

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {g : X' ⟶ X}
    {Â : ∀ T : BigFppfOver B S hS, (yoneda.obj T ⟶ X) →
      SheafGradedAlgebra ((BigFppfOver.toScheme B S hS).obj T)}
    {Â' : ∀ T : BigFppfOver B S hS, (yoneda.obj T ⟶ X') →
      SheafGradedAlgebra ((BigFppfOver.toScheme B S hS).obj T)}
    {ρ₁ : GradedAlgebraRestriction (GradedAlgebraPoints.ofQuasicoherentFamily Â)}
    {ρ₁' : GradedAlgebraRestriction (GradedAlgebraPoints.ofQuasicoherentFamily Â')}
    (e₁ : ComapHom ρ₁' ρ₁ g)
    (hc : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      B.Contains (relativeProj (Â T f)).scheme)
    (hc' : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X'),
      B.Contains (relativeProj (Â' T f)).scheme)

/-- The point of the image of the tautological point of `Proj_T(f'^*𝒜')`. -/
theorem limPointMap_projPoint_point {T : BigFppfOver B S hS} (f' : yoneda.obj T ⟶ X') :
    (e₁.limPointMap (ρ₁'.projPoint f' (hc' T f') (𝟙 _))).point =
      yoneda.map (projHom Â' f' (hc' T f')) ≫ f' ≫ g := by
  rw [limPointMap_point, projPoint_point, Category.id_comp, Category.assoc]

/-- **The fibre map of a comparison of restriction data**: the morphism
`Proj_T(f'^*𝒜') ⟶ Proj_T((g ∘ f')^*𝒜)` over `T` corresponding to the image under
`F' ⟶ F` of the tautological point of `Proj_T(f'^*𝒜')`. -/
def projMap {T : BigFppfOver B S hS} (f' : yoneda.obj T ⟶ X') :
    projObj Â' f' (hc' T f') ⟶ projObj Â (f' ≫ g) (hc T (f' ≫ g)) :=
  ρ₁.projHomOf (f' ≫ g) (hc T (f' ≫ g)) (projHom Â' f' (hc' T f'))
    (e₁.limPointMap (ρ₁'.projPoint f' (hc' T f') (𝟙 _))) (e₁.limPointMap_projPoint_point hc' f')

/-- The fibre map lies over `T`. -/
theorem projMap_comp_projHom {T : BigFppfOver B S hS} (f' : yoneda.obj T ⟶ X') :
    e₁.projMap hc hc' f' ≫ projHom Â (f' ≫ g) (hc T (f' ≫ g)) = projHom Â' f' (hc' T f') :=
  ρ₁.projHomOf_comp_projHom _ _ _ _ _

/-- The fibre map lies over the morphism `F' ⟶ F` of the functors of quadruples. -/
theorem map_projMap_comp_projToFunctor {T : BigFppfOver B S hS} (f' : yoneda.obj T ⟶ X') :
    yoneda.map (e₁.projMap hc hc' f') ≫ ρ₁.projToFunctor hc (f' ≫ g) =
      ρ₁'.projToFunctor hc' f' ≫ e₁.relativeProjMap hc hc' := by
  apply yonedaEquiv.injective
  apply (ρ₁.relativeProjFunctorEquiv hc _).injective
  rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map,
    relativeProjFunctorEquiv_projToFunctor, relativeProjFunctorEquiv_relativeProjMap]
  simp only [projToFunctor, Equiv.apply_symm_apply]
  rw [projMap, projPoint_projHomOf]

/-- The fibre map lies over the morphism `F' ⟶ F` of the functors of quadruples of Stacks 084A. -/
theorem map_projMap_comp_projToQuadrupleSpace
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X') {T : BigFppfOver B S hS}
    (f' : yoneda.obj T ⟶ X') :
    yoneda.map (e₁.projMap hc hc' f') ≫ ρ₁.projToQuadrupleSpace hc hX (f' ≫ g) =
      ρ₁'.projToQuadrupleSpace hc' hX' f' ≫ e₁.quadrupleSpaceMap hc hc' hX hX' := by
  rw [projToQuadrupleSpace, projToQuadrupleSpace, quadrupleSpaceMap, ← Category.assoc,
    map_projMap_comp_projToFunctor]
  simp

set_option synthInstance.maxHeartbeats 400000 in
/-- **On schemes, the fibre map is the identification of relative Projs along the comparison of
the algebras.** -/
theorem toScheme_map_projMap {T : BigFppfOver B S hS} (f' : yoneda.obj T ⟶ X') :
    (BigFppfOver.toScheme B S hS).map (e₁.projMap hc hc' f') =
      (relativeProjCongr (A₁ := Â' T f') (A₂ := Â T (f' ≫ g)) (e₁.hom f')
        (e₁.isIso_hom_app f')).hom := by
  apply (relativeProjRepresentableByFunctorUnconditional (Â T (f' ≫ g))).homEquiv.injective
  apply (Scheme.QcExtension.equivQcOpen _ _).injective
  ext V hV
  have hO : CompactSpace ((BigFppfOver.toScheme B S hS).obj
      (opensObject B S hS (projObj Â' f' (hc' T f')) V)) :=
    isCompact_iff_compactSpace.mp hV
  change ((relativeProjRepresentableByFunctorUnconditional (Â T (f' ≫ g))).homEquiv
      ((BigFppfOver.toScheme B S hS).map (e₁.projMap hc hc' f'))).val _ hO
      ((BigFppfOver.toScheme B S hS).map (opensObjectι B S hS (projObj Â' f' (hc' T f')) V)) =
    ((relativeProjRepresentableByFunctorUnconditional (Â T (f' ≫ g))).homEquiv
      (relativeProjCongr (A₁ := Â' T f') (A₂ := Â T (f' ≫ g)) (e₁.hom f')
        (e₁.isIso_hom_app f')).hom).val _ hO
      ((BigFppfOver.toScheme B S hS).map (opensObjectι B S hS (projObj Â' f' (hc' T f')) V))
  set ι := opensObjectι B S hS (projObj Â' f' (hc' T f')) V with hι
  set p := ρ₁'.projPoint f' (hc' T f') (𝟙 _) with hp
  have hk : (relativeProjRepresentableByFunctorUnconditional (Â T (f' ≫ g))).homEquiv
      ((BigFppfOver.toScheme B S hS).map (e₁.projMap hc hc' f')) =
      ρ₁.qcOfLimPoint (f' ≫ g) (projHom Â' f' (hc' T f')) (e₁.limPointMap p)
        (e₁.limPointMap_projPoint_point hc' f') :=
    Equiv.apply_symm_apply _ _
  have step1 := (congrArg (fun z : Scheme.QcExtension (F.functor (situationAlgebra (Â T (f' ≫ g))))
      ((BigFppfOver.toScheme B S hS).obj (projObj Â' f' (hc' T f'))) => z.val _ hO
        ((BigFppfOver.toScheme B S hS).map ι)) hk).trans
    (ρ₁.qcOfLimPoint_val (f' ≫ g) (projHom Â' f' (hc' T f')) (e₁.limPointMap p)
      (e₁.limPointMap_projPoint_point hc' f') _ hO ι)
  have hf : yoneda.map (ι ≫ projHom Â' f' (hc' T f')) ≫ f' = yoneda.map ι ≫ p.point := by
    rw [hp, projPoint_point, Category.id_comp, Functor.map_comp, Category.assoc]
  have step2 := e₁.fibreToF_fibreInv f' (ι ≫ projHom Â' f' (hc' T f')) (yoneda.map ι ≫ p.point) hf
    (by rw [← Category.assoc, hf]) (p.val _ hO ι)
  have step3 := (ρ₁'.fibreToF_congr f' (show ι ≫ projHom Â' f' (hc' T f') =
      ι ≫ 𝟙 _ ≫ projHom Â' f' (hc' T f') by rw [Category.id_comp])
    (yoneda.map ι ≫ p.point) hf (by simpa using hf) (p.val _ hO ι)).trans
    (ρ₁'.fibreToF_projPoint_val hc' f' (𝟙 _) _ hO ι)
  have step4 := homEquiv_comp_relativeProjCongr_val (A₁ := Â' T f') (A₂ := Â T (f' ≫ g))
    (e₁.hom f') (e₁.isIso_hom_app f') (𝟙 _) _ hO ((BigFppfOver.toScheme B S hS).map ι)
  rw [Category.id_comp] at step4
  exact (step1.trans step2).trans ((congrArg (fun z => F.algebraTransport
    (unitalHomInverse (e₁.hom f') (e₁.isIso_hom_app f'))
    (isIso_unitalHomInverse_app _ _) z) step3).trans step4.symm)

end ProjMap

end ComapHom

end GradedAlgebraRestriction

/-! ### Morphisms of base changes along a morphism of relative Projs -/

namespace RelativeProjPoints

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X X' P P' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : P ⟶ X} {π' : P' ⟶ X'}
  (d' : RelativeProjPoints B S hS π') (d : RelativeProjPoints B S hS π) (h : P' ⟶ P)

/-- A morphism `T' ×_{X'} P' ⟶ T ×_X P` of base changes **lies over** a morphism `k : T' ⟶ T` of
test objects **and over** `h : P' ⟶ P` if it commutes with the structure morphisms to `T'` and
`T` and with the morphisms to `P'` and `P`. -/
def LiesOverAlong {T T' : BigFppfOver B S hS} {f : yoneda.obj T ⟶ X} {f' : yoneda.obj T' ⟶ X'}
    (y : d'.fibre T' f' ⟶ d.fibre T f) (k : T' ⟶ T) : Prop :=
  y ≫ d.fibreHom T f = d'.fibreHom T' f' ≫ k ∧
    yoneda.map y ≫ d.fibreToSpace T f = d'.fibreToSpace T' f' ≫ h

variable {d' d h}

/-- Two morphisms lying over the same morphisms agree. -/
theorem LiesOverAlong.eq {T T' : BigFppfOver B S hS} {f : yoneda.obj T ⟶ X}
    {f' : yoneda.obj T' ⟶ X'} {y₁ y₂ : d'.fibre T' f' ⟶ d.fibre T f} {k₁ k₂ : T' ⟶ T}
    (hy₁ : d'.LiesOverAlong d h y₁ k₁) (hy₂ : d'.LiesOverAlong d h y₂ k₂) (hk : k₁ = k₂) :
    y₁ = y₂ :=
  d.fibre_hom_ext (by rw [hy₁.1, hy₂.1, hk]) (by rw [hy₁.2, hy₂.2])

/-- Lying over is compatible with a further morphism of base changes of `P`. -/
theorem LiesOverAlong.comp_liesOver {T T' T₀ : BigFppfOver B S hS} {f : yoneda.obj T ⟶ X}
    {f' : yoneda.obj T' ⟶ X'} {f₀ : yoneda.obj T₀ ⟶ X} {y : d'.fibre T' f' ⟶ d.fibre T f}
    {x : d.fibre T f ⟶ d.fibre T₀ f₀} {k : T' ⟶ T} {k₀ : T ⟶ T₀}
    (hy : d'.LiesOverAlong d h y k) (hx : d.LiesOver x k₀) :
    d'.LiesOverAlong d h (y ≫ x) (k ≫ k₀) :=
  ⟨by rw [Category.assoc, hx.1, ← Category.assoc, hy.1, Category.assoc],
    by rw [Functor.map_comp, Category.assoc, hx.2, hy.2]⟩

/-- Lying over is compatible with a previous morphism of base changes of `P'`. -/
theorem LiesOver.comp_liesOverAlong {T T' T'' : BigFppfOver B S hS} {f : yoneda.obj T ⟶ X}
    {f' : yoneda.obj T' ⟶ X'} {f'' : yoneda.obj T'' ⟶ X'} {x' : d'.fibre T'' f'' ⟶ d'.fibre T' f'}
    {y : d'.fibre T' f' ⟶ d.fibre T f} {k' : T'' ⟶ T'} {k : T' ⟶ T}
    (hx' : d'.LiesOver x' k') (hy : d'.LiesOverAlong d h y k) :
    d'.LiesOverAlong d h (x' ≫ y) (k' ≫ k) :=
  ⟨by rw [Category.assoc, hy.1, ← Category.assoc, hx'.1, Category.assoc],
    by rw [Functor.map_comp, Category.assoc, hy.2, ← Category.assoc, hx'.2]⟩

variable (d' d h) in
/-- **The morphism of base changes along `h`**: for `h ≫ π = π' ≫ g` and `u ∘ k = g ∘ f'`, the
morphism `T' ×_{X'} P' ⟶ T ×_X P` induced by `k` and `h`. -/
def fibreMapAlong {g : X' ⟶ X} (hπ : h ≫ π = π' ≫ g) {T T' : BigFppfOver B S hS}
    (f : yoneda.obj T ⟶ X) (f' : yoneda.obj T' ⟶ X') (k : T' ⟶ T)
    (hk : yoneda.map k ≫ f = f' ≫ g) : d'.fibre T' f' ⟶ d.fibre T f :=
  d.fibreLift (d'.fibreHom T' f' ≫ k) (d'.fibreToSpace T' f' ≫ h) (by
    rw [Category.assoc, hπ, ← Category.assoc, (d'.isPullback T' f').w, Functor.map_comp,
      Category.assoc, Category.assoc, hk])

/-- The morphism of base changes along `h` lies over `k` and `h`. -/
theorem liesOverAlong_fibreMapAlong {g : X' ⟶ X} (hπ : h ≫ π = π' ≫ g)
    {T T' : BigFppfOver B S hS} (f : yoneda.obj T ⟶ X) (f' : yoneda.obj T' ⟶ X') (k : T' ⟶ T)
    (hk : yoneda.map k ≫ f = f' ≫ g) :
    d'.LiesOverAlong d h (fibreMapAlong d' d h hπ f f' k hk) k :=
  ⟨d.fibreLift_comp_fibreHom _ _ _, d.map_fibreLift_comp_fibreToSpace _ _ _⟩

/-- Two composites, through a morphism of base changes of `P` and of `P'` respectively, lying over
equal composites, agree. -/
theorem LiesOverAlong.comp_eq_comp {T T' T₀ T₀' : BigFppfOver B S hS} {f : yoneda.obj T ⟶ X}
    {f' : yoneda.obj T' ⟶ X'} {f₀ : yoneda.obj T₀ ⟶ X} {f₀' : yoneda.obj T₀' ⟶ X'}
    {y₁ : d'.fibre T' f' ⟶ d.fibre T f} {x₁ : d.fibre T f ⟶ d.fibre T₀ f₀}
    {x₂ : d'.fibre T' f' ⟶ d'.fibre T₀' f₀'} {y₂ : d'.fibre T₀' f₀' ⟶ d.fibre T₀ f₀}
    {k₁ : T' ⟶ T} {k₀ : T ⟶ T₀} {k₂ : T' ⟶ T₀'} {k₃ : T₀' ⟶ T₀}
    (hy₁ : d'.LiesOverAlong d h y₁ k₁) (hx₁ : d.LiesOver x₁ k₀) (hx₂ : d'.LiesOver x₂ k₂)
    (hy₂ : d'.LiesOverAlong d h y₂ k₃) (hk : k₁ ≫ k₀ = k₂ ≫ k₃) : y₁ ≫ x₁ = x₂ ≫ y₂ :=
  (hy₁.comp_liesOver hx₁).eq (hx₂.comp_liesOverAlong hy₂) hk

section PresentationAlong

variable {XA XA' : AlgebraicSpaces B S hS} {PA PA' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {πA : PA ⟶ XA.obj} {πA' : PA' ⟶ XA'.obj} {dA : RelativeProjPoints B S hS πA}
  {dA' : RelativeProjPoints B S hS πA'} {hA : PA' ⟶ PA} {gA : XA'.obj ⟶ XA.obj}
  (hπA : hA ≫ πA = πA' ≫ gA) (Px : Presentation B S hS XA.obj XA.property)
  (Px' : Presentation B S hS XA'.obj XA'.property) (hP : IsAlgebraicSpace B S hS PA)
  (hP' : IsAlgebraicSpace B S hS PA') (ℓ : Px'.U ⟶ Px.U)
  (hℓ : yoneda.map ℓ ≫ Px.toSpace = Px'.toSpace ≫ gA) (ℓR : Px'.R ⟶ Px.R)
  (hℓR : yoneda.map ℓR ≫ relationPoint Px = relationPoint Px' ≫ gA)

include hπA in
/-- The morphisms of the presenting schemes along `h` commute with the target projections. -/
theorem presentationTarget_comp_fibreMapAlong (hℓt : ℓR ≫ Px.target = Px'.target ≫ ℓ) :
    (dA'.presentation Px' hP').target ≫ fibreMapAlong dA' dA hA hπA Px.toSpace Px'.toSpace ℓ hℓ =
      fibreMapAlong dA' dA hA hπA (relationPoint Px) (relationPoint Px') ℓR hℓR ≫
        (dA.presentation Px hP).target :=
  (LiesOverAlong.comp_eq_comp (liesOverAlong_fibreMapAlong hπA _ _ ℓR hℓR)
    (dA.liesOver_spaceTarget Px hP) (dA'.liesOver_spaceTarget Px' hP')
    (liesOverAlong_fibreMapAlong hπA _ _ ℓ hℓ) hℓt).symm

include hπA in
/-- The morphisms of the presenting schemes along `h` commute with the source projections. -/
theorem fibreMapAlong_comp_presentationSource (hℓs : ℓR ≫ Px.source = Px'.source ≫ ℓ) :
    fibreMapAlong dA' dA hA hπA (relationPoint Px) (relationPoint Px') ℓR hℓR ≫
        (dA.presentation Px hP).source =
      (dA'.presentation Px' hP').source ≫
        fibreMapAlong dA' dA hA hπA Px.toSpace Px'.toSpace ℓ hℓ :=
  LiesOverAlong.comp_eq_comp (liesOverAlong_fibreMapAlong hπA _ _ ℓR hℓR)
    (dA.liesOver_spaceSource Px hP) (dA'.liesOver_spaceSource Px' hP')
    (liesOverAlong_fibreMapAlong hπA _ _ ℓ hℓ) hℓs

end PresentationAlong

end RelativeProjPoints

end AlgebraicGeometry.Space

end
