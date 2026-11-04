module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackGlue
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackCanonicalArrow
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.SecondOrder
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.SpaceLiftCover

/-!
# The lifting step for a stack, from a chart point over a covering

Let `𝒳` be a stack in groupoids over the big fppf site with a chart `(a, ι)` by a small
`A'`-algebra `P` over the affine object `T'`, `A' = Γ(T', ⊤)`, whose groupoid is formally smooth
on sources and has a formally étale chart near the identities. Let `C'` be a faithfully flat
finitely presented `A'`-algebra and `I ⊆ A'` a square-zero ideal. An object `x̄` of `𝒳` over
`Spec (A' ⧸ I)` that comes, over `Spec (C' ⧸ I C')`, from a point `ū` of the chart, extends to an
object over `Spec A'`
(`AlgebraicGeometry.Stack.GroupoidLift.StackChart.exists_lift_of_chartPoint`).

The descent arrow of `x̄` relative to the covering is the canonical arrow of the two pullbacks of
the chart identification (`AlgebraicGeometry.Stack.GroupoidLift.StackChart.chartNerveDatum`). By
`AlgebraicGeometry.Stack.GroupoidLift.NerveDatum.exists_lift_arrow_cocycle`, the point and the
arrow lift with an exact cocycle, the arrow descends
(`AlgebraicGeometry.Stack.GroupoidLift.StackChart.exists_descent_of_hom`), and the descended object
receives `x̄` (`AlgebraicGeometry.Stack.GroupoidLift.StackChart.exists_hom_of_chart`).

## Main results

* `AlgebraicGeometry.Stack.GroupoidLift.StackChart.exists_lift_of_chartPoint`.
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory Opposite Limits
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe w u

section Algebra

variable {A' : Type u} [CommRing A'] {κ : Cardinal.{u}} (I : Ideal A')

/-- The reduction of an algebra map, as a morphism of small algebras. -/
abbrev redHom {N N' : SmallAlg A' κ} (f : N.obj →ₐ[A'] N'.obj) : red I N ⟶ red I N' :=
  SmallAlg.homMk (redMap I f)

/-- The reduction of a composite of algebra maps is the composite of the reductions. -/
theorem redHom_comp {N N' N'' : SmallAlg A' κ} (f : N.obj →ₐ[A'] N'.obj)
    (g : N'.obj →ₐ[A'] N''.obj) :
    redHom I (N := N) (N' := N') f ≫ redHom I (N' := N'') g = redHom I (N' := N'') (g.comp f) :=
  ObjectProperty.hom_ext _ (CommAlgCat.hom_ext (redMap_comp I f g))

/-- Equal algebra maps have equal reductions. -/
theorem redHom_congr {N N' : SmallAlg A' κ} {f g : N.obj →ₐ[A'] N'.obj} (h : f = g) :
    redHom I (N := N) (N' := N') f = redHom I g := by
  rw [h]

/-- The reduction of the identity algebra map is the identity. -/
theorem redHom_id (N : SmallAlg A' κ) : redHom I (N := N) (N' := N) (AlgHom.id A' _) = 𝟙 _ :=
  ObjectProperty.hom_ext _ (CommAlgCat.hom_ext (redMap_id I N))

/-- If `g ∘ f = g' ∘ f'`, then the composites of the reductions agree. -/
theorem redHom_comp_eq {N N' N'' M : SmallAlg A' κ} (f : N.obj →ₐ[A'] N'.obj)
    (g : N'.obj →ₐ[A'] N''.obj) (f' : N.obj →ₐ[A'] M.obj) (g' : M.obj →ₐ[A'] N''.obj)
    (h : g.comp f = g'.comp f') :
    redHom I (N := N) (N' := N') f ≫ redHom I (N' := N'') g = redHom I (N' := M) f' ≫ redHom I g' :=
  (redHom_comp I f g).trans ((redHom_congr I h).trans (redHom_comp I f' g').symm)

/-- If `g ∘ f` is the identity, then the composite of the reductions is the identity. -/
theorem redHom_comp_eq_id {N N' : SmallAlg A' κ} (f : N.obj →ₐ[A'] N'.obj)
    (g : N'.obj →ₐ[A'] N.obj) (h : g.comp f = AlgHom.id A' _) :
    redHom I (N := N) (N' := N') f ≫ redHom I (N' := N) g = 𝟙 _ :=
  (redHom_comp I f g).trans ((redHom_congr I h).trans (redHom_id I N))

/-- Two morphisms out of the reduction of the base algebra `A' ⧸ I` are equal. -/
theorem red_hom_ext (hA : Cardinal.mk A' < κ) {N : SmallAlg A' κ} (f g : red I (baseAlg hA) ⟶ N) :
    f = g :=
  GroupoidLift.SmallAlg.hom_ext_of_surjective (fun x ↦ by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨y, rfl⟩) f g

end Algebra

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {U₀ : BigFppfOver B S hS} {a : schemeFibredCategory B S hS U₀ ⟶ 𝒳}
  {P : SmallAlg (ringOf B S hS T') B.cutoff} {ι : specOver P ⟶ U₀}

namespace StackChart

/-- For a commutative square `h ≫ g = h' ≫ g'` of small algebras, the composites of the transport
isomorphisms along the two sides agree, up to `eqToHom`. -/
theorem trans_square {C D D' E : SmallAlg (ringOf B S hS T') B.cutoff} (h : C ⟶ D) (g : D ⟶ E)
    (h' : C ⟶ D') (g' : D' ⟶ E) (e : h ≫ g = h' ≫ g') (w : P.obj →ₐ[ringOf B S hS T'] C.obj)
    (hX : ξ a ι (g.hom.hom.comp (h.hom.hom.comp w)) = ξ a ι (g'.hom.hom.comp (h'.hom.hom.comp w))) :
    trans a ι g (h.hom.hom.comp w) ≫ trans a ι h w =
      eqToHom hX ≫ trans a ι g' (h'.hom.hom.comp w) ≫ trans a ι h' w :=
  (trans_comp a ι h g w).symm.trans ((trans_eq_of_eq (a := a) (ι := ι) e w).trans
    (congrArg _ (trans_comp a ι h' g' w)))

/-- `trans_square`, post-composed with a morphism `c`. -/
private theorem trans_square_assoc {C D D' E : SmallAlg (ringOf B S hS T') B.cutoff}
    (h : C ⟶ D) (g : D ⟶ E) (h' : C ⟶ D') (g' : D' ⟶ E) (e : h ≫ g = h' ≫ g')
    (w : P.obj →ₐ[ringOf B S hS T'] C.obj)
    (hX : ξ a ι (g.hom.hom.comp (h.hom.hom.comp w)) = ξ a ι (g'.hom.hom.comp (h'.hom.hom.comp w)))
    {Z : 𝒳.val.obj} (c : ξ a ι w ⟶ Z) :
    trans a ι g (h.hom.hom.comp w) ≫ trans a ι h w ≫ c =
      eqToHom hX ≫ trans a ι g' (h'.hom.hom.comp w) ≫ trans a ι h' w ≫ c :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ c) (trans_square h g h' g' e w hX)).trans
    ((Category.assoc _ _ _).trans (congrArg _ (Category.assoc _ _ _))))

/-- A morphism lying over `m` lies over any `m'` equal to `m`. -/
theorem isHomLift_of_eq {W W' : BigFppfOver B S hS} {m m' : W ⟶ W'} (e : m = m')
    {x y : 𝒳.val.obj} {φ : x ⟶ y} (h : 𝒳.val.p.IsHomLift m φ) : 𝒳.val.p.IsHomLift m' φ :=
  e ▸ h

/-- The canonical arrow does not depend on the chosen base morphism, up to equality. -/
theorem canArr_base_congr {C : SmallAlg (ringOf B S hS T') B.cutoff} {y : 𝒳.val.obj}
    {W : BigFppfOver B S hS} {m m' : specOver C ⟶ W} (e : m = m')
    {w₁ w₂ : P.obj →ₐ[ringOf B S hS T'] C.obj} (c₁ : ξ a ι w₁ ⟶ y) (c₂ : ξ a ι w₂ ⟶ y)
    (h₁ : 𝒳.val.p.IsHomLift m c₁) (h₂ : 𝒳.val.p.IsHomLift m c₂) :
    canArr m w₁ w₂ c₁ c₂ h₁ h₂ =
      canArr m' w₁ w₂ c₁ c₂ (isHomLift_of_eq e h₁) (isHomLift_of_eq e h₂) := by
  subst e
  rfl

/-- Composition of arrows respects equality of both factors. -/
theorem Arr.comp_congr {C : SmallAlg (ringOf B S hS T') B.cutoff} {g g' f f' : Arr a ι C}
    (hg : g = g') (hf : f = f') (h : g.src = f.tgt) :
    Arr.comp g f h = Arr.comp g' f' (hg ▸ hf ▸ h) := by
  subst hg hf
  rfl

section Nerve

variable (hA : Cardinal.mk (ringOf B S hS T') < B.cutoff) {C' : Type u} [CommRing C']
  [Algebra (ringOf B S hS T') C'] (hC : Cardinal.mk C' < B.cutoff) (I : Ideal (ringOf B S hS T'))
  (hI : I ^ 2 = ⊥)

/-- The reduced vertex `0` of the double overlap. -/
abbrev rV₀ : red I (descNerve T' hC 0) ⟶ red I (descNerve T' hC 1) :=
  redHom I (v₀ (ringOf B S hS T') C' 1)

/-- The reduced last vertex of the double overlap. -/
abbrev rVₗ : red I (descNerve T' hC 0) ⟶ red I (descNerve T' hC 1) :=
  redHom I (vₗ (ringOf B S hS T') C' 1)

/-- The reduced faces. -/
abbrev rFace (i : Fin 3) : red I (descNerve T' hC 1) ⟶ red I (descNerve T' hC 2) :=
  redHom I (face (ringOf B S hS T') C' 1 i)

/-- The reduced codegeneracy. -/
abbrev rCodeg : red I (descNerve T' hC 1) ⟶ red I (descNerve T' hC 0) :=
  redHom I (codeg (ringOf B S hS T') C' 0)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- The reduced vertices and faces satisfy `rV₀ ≫ rFace 0 = rVₗ ≫ rFace 2`. -/
theorem rV₀_face_zero : rV₀ hC I ≫ rFace hC I 0 = rVₗ hC I ≫ rFace hC I 2 :=
  redHom_comp_eq I _ _ _ _ (AlgHom.ext fun _ ↦ rfl)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- The reduced vertices and faces satisfy `rV₀ ≫ rFace 1 = rV₀ ≫ rFace 2`. -/
theorem rV₀_face_one : rV₀ hC I ≫ rFace hC I 1 = rV₀ hC I ≫ rFace hC I 2 :=
  redHom_comp_eq I _ _ _ _ (AlgHom.ext fun _ ↦ rfl)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- The reduced vertices and faces satisfy `rVₗ ≫ rFace 1 = rVₗ ≫ rFace 0`. -/
theorem rVₗ_face_one : rVₗ hC I ≫ rFace hC I 1 = rVₗ hC I ≫ rFace hC I 0 :=
  redHom_comp_eq I _ _ _ _ (AlgHom.ext fun _ ↦ rfl)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- The reduced codegeneracy is a retraction of the reduced vertex `0`. -/
theorem rV₀_codeg : rV₀ hC I ≫ rCodeg hC I = 𝟙 _ :=
  redHom_comp_eq_id I _ _ (codeg_comp_face_one 0)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- The reduced codegeneracy is a retraction of the reduced last vertex. -/
theorem rVₗ_codeg : rVₗ hC I ≫ rCodeg hC I = 𝟙 _ :=
  redHom_comp_eq_id I _ _ (codeg_comp_vₗ 0)

/-- The two reduced vertices of the double overlap agree after composing with the map to the
reduced base. -/
theorem spec_rV_base :
    specOverMap (rVₗ hC I) ≫ specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot =
      specOverMap (rV₀ hC I) ≫ specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot :=
  (specOverMap_comp _ _).symm.trans ((congrArg specOverMap (red_hom_ext I hA _ _)).trans
    (specOverMap_comp _ _))

variable {hA hI} {xb : 𝒳.val.obj}
  (ubar : P.obj →ₐ[ringOf B S hS T'] (red I (descNerve T' hC 0)).obj) (c : ξ a ι ubar ⟶ xb)
  [hc : 𝒳.val.p.IsHomLift (specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot) c]

/-- The second pullback of `c` lies over the first reduced vertex composed with the base map. -/
private theorem isHomLift_rVₗ_base :
    𝒳.val.p.IsHomLift (specOverMap (rV₀ hC I) ≫
      specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot) (trans a ι (rVₗ hC I) ubar ≫ c) :=
  isHomLift_of_eq (spec_rV_base hA hC I hI) inferInstance

/-- **The descent arrow of `x̄` relative to the covering**: the canonical arrow between the two
pullbacks of the chart identification `c : ξ ū ⟶ x̄`. -/
noncomputable def chartRbar : Arr a ι (red I (descNerve T' hC 1)) :=
  canArr (specOverMap (rV₀ hC I) ≫ specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot)
    ((rV₀ hC I).hom.hom.comp ubar) ((rVₗ hC I).hom.hom.comp ubar)
    (trans a ι (rV₀ hC I) ubar ≫ c) (trans a ι (rVₗ hC I) ubar ≫ c) inferInstance
    (isHomLift_of_eq (spec_rV_base hA hC I hI) inferInstance)

/-- The descent arrow of `x̄` composed with the second pullback of `c` is the first pullback of
`c`. -/
theorem chartRbar_fac : (chartRbar hC I ubar c).hom ≫ trans a ι (rVₗ hC I) ubar ≫ c =
    trans a ι (rV₀ hC I) ubar ≫ c :=
  canArr_fac _ _ _ _ _

/-- The descent arrow of `x̄` restricts to the identity along the reduced codegeneracy. -/
theorem chartRbar_norm : Arr.map a ι (rCodeg hC I) (chartRbar hC I ubar c) = Arr.idt ubar := by
  have h₂ := isHomLift_rVₗ_base hC I ubar c
  refine (map_canArr _ _ _ _ _ _ inferInstance inferInstance).trans ?_
  refine canArr_eq_idt _ _ _ _ _
    ((congrArg (fun m : _ ⟶ red I (descNerve T' hC 0) ↦ m.hom.hom.comp ubar) (rV₀_codeg hC I)))
    ((congrArg (fun m : _ ⟶ red I (descNerve T' hC 0) ↦ m.hom.hom.comp ubar) (rVₗ_codeg hC I))) ?_
  exact trans_square_assoc _ _ _ _ ((rV₀_codeg hC I).trans (rVₗ_codeg hC I).symm) ubar _ c

/-- Two morphisms out of the reduction of the base algebra induce equal morphisms of spectra. -/
theorem spec_red_base_eq {N : SmallAlg (ringOf B S hS T') B.cutoff}
    (k k' : red I (baseAlg hA) ⟶ N) :
    specOverMap k = specOverMap k' :=
  congrArg specOverMap (red_hom_ext I hA k k')

/-- The composite of a reduced face, the reduced vertex `0` and the map to the reduced base does
not depend on the face. -/
theorem chartRbar_face_base (i : Fin 3) :
    specOverMap (rFace hC I i) ≫ specOverMap (rV₀ hC I) ≫
        specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot =
      specOverMap (rFace hC I 1) ≫ specOverMap (rV₀ hC I) ≫
        specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot :=
  (congrArg (specOverMap (rFace hC I i) ≫ ·) (specOverMap_comp _ _).symm).trans
    ((specOverMap_comp _ _).symm.trans ((spec_red_base_eq _ _ _).trans
      ((specOverMap_comp _ _).trans (congrArg (specOverMap (rFace hC I 1) ≫ ·)
        (specOverMap_comp _ _)))))

include hc in
/-- The image of the descent arrow of `x̄` under a reduced face is the canonical arrow of the
pullbacks of `c` along that face. -/
theorem chartRbar_map (i : Fin 3) :
    Arr.map a ι (rFace hC I i) (chartRbar hC I ubar c) =
      canArr (specOverMap (rFace hC I 1) ≫ specOverMap (rV₀ hC I) ≫
          specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot)
        ((rFace hC I i).hom.hom.comp ((rV₀ hC I).hom.hom.comp ubar))
        ((rFace hC I i).hom.hom.comp ((rVₗ hC I).hom.hom.comp ubar))
        (trans a ι (rFace hC I i) _ ≫ trans a ι (rV₀ hC I) ubar ≫ c)
        (trans a ι (rFace hC I i) _ ≫ trans a ι (rVₗ hC I) ubar ≫ c)
        (isHomLift_of_eq (chartRbar_face_base hC I i) inferInstance)
        (isHomLift_of_eq
          ((congrArg (specOverMap (rFace hC I i) ≫ ·) (spec_rV_base hA hC I hI)).trans
            (chartRbar_face_base hC I i)) inferInstance) := by
  have h₂ := isHomLift_rVₗ_base hC I ubar c
  exact (map_canArr _ _ _ _ _ _ inferInstance inferInstance).trans
    (canArr_base_congr (chartRbar_face_base hC I i) _ _ _ _)

include hc in
/-- **The cocycle condition** for the descent arrow of `x̄`. -/
theorem chartRbar_cocycle :
    ∃ h : (Arr.map a ι (rFace hC I 0) (chartRbar hC I ubar c)).src =
        (Arr.map a ι (rFace hC I 2) (chartRbar hC I ubar c)).tgt,
      Arr.comp (Arr.map a ι (rFace hC I 0) (chartRbar hC I ubar c))
        (Arr.map a ι (rFace hC I 2) (chartRbar hC I ubar c)) h =
        Arr.map a ι (rFace hC I 1) (chartRbar hC I ubar c) := by
  have h : (Arr.map a ι (rFace hC I 0) (chartRbar hC I ubar c)).src =
      (Arr.map a ι (rFace hC I 2) (chartRbar hC I ubar c)).tgt :=
    congrArg (fun m : red I (descNerve T' hC 0) ⟶ red I (descNerve T' hC 2) ↦ m.hom.hom.comp ubar)
      (rV₀_face_zero hC I)
  refine ⟨h, ?_⟩
  refine (Arr.comp_congr (chartRbar_map hC I ubar c 0) (chartRbar_map hC I ubar c 2) h).trans
    ((comp_canArr _ _ _ _ _ _ _ _ _ h ?_).trans
      ((canArr_congr _ _ _ _ _ _ _ _ _
        (congrArg
          (fun m : red I (descNerve T' hC 0) ⟶ red I (descNerve T' hC 2) ↦ m.hom.hom.comp ubar)
          (rV₀_face_one hC I).symm)
        (congrArg
          (fun m : red I (descNerve T' hC 0) ⟶ red I (descNerve T' hC 2) ↦ m.hom.hom.comp ubar)
          (rVₗ_face_one hC I).symm) ?_ ?_).trans (chartRbar_map hC I ubar c 1).symm))
  · exact trans_square_assoc _ _ _ _ (rV₀_face_zero hC I) ubar _ c
  · exact trans_square_assoc _ _ _ _ (rV₀_face_one hC I).symm ubar _ c
  · exact trans_square_assoc _ _ _ _ (rVₗ_face_one hC I).symm ubar _ c

end Nerve

section Lift

variable (hA : Cardinal.mk (ringOf B S hS T') < B.cutoff) {C' : Type u} [CommRing C']
  [Algebra (ringOf B S hS T') C'] (hC : Cardinal.mk C' < B.cutoff) (I : Ideal (ringOf B S hS T'))
  (hI : I ^ 2 = ⊥)

/-- The reduction map of the covering algebra. -/
abbrev qC : descNerve T' hC 0 ⟶ red I (descNerve T' hC 0) :=
  (thk I hI (descNerve T' hC 0)).q

/-- The reduction map of the double overlap. -/
abbrev qC₁ : descNerve T' hC 1 ⟶ red I (descNerve T' hC 1) :=
  (thk I hI (descNerve T' hC 1)).q

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- Reduction commutes with the last vertex of the double overlap. -/
theorem qC_rVₗ : qC hC I hI ≫ rVₗ hC I = descVₗ T' hC ≫ qC₁ hC I hI :=
  ObjectProperty.hom_ext _ (CommAlgCat.hom_ext (AlgHom.ext fun _ ↦ rfl))

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- Reduction commutes with the vertex `0` of the double overlap. -/
theorem qC_rV₀ : qC hC I hI ≫ rV₀ hC I = descV₀ T' hC ≫ qC₁ hC I hI :=
  ObjectProperty.hom_ext _ (CommAlgCat.hom_ext (AlgHom.ext fun _ ↦ rfl))

variable {hC I hI} (u : P.obj →ₐ[ringOf B S hS T'] (descNerve T' hC 0).obj)
  (hom : ξ a ι ((descV₀ T' hC).hom.hom.comp u) ⟶ ξ a ι ((descVₗ T' hC).hom.hom.comp u))
  [lift : 𝒳.val.p.IsHomLift (𝟙 (specOver (descNerve T' hC 1))) hom]

/-- **The reduction of the descended arrow intertwines the descended object.** -/
theorem red_descArr_fac {x' : 𝒳.val.obj} (ζ : ξ a ι u ⟶ x')
    (hζ : hom ≫ trans a ι (descVₗ T' hC) u ≫ ζ = trans a ι (descV₀ T' hC) u ≫ ζ)
    (ρ : ξ a ι ((rV₀ hC I).hom.hom.comp ((qC hC I hI).hom.hom.comp u)) ⟶
      ξ a ι ((rVₗ hC I).hom.hom.comp ((qC hC I hI).hom.hom.comp u)))
    (h₁ : ξ a ι ((rV₀ hC I).hom.hom.comp ((qC hC I hI).hom.hom.comp u)) =
      ξ a ι ((qC₁ hC I hI).hom.hom.comp ((descV₀ T' hC).hom.hom.comp u)))
    (h₂ : ξ a ι ((qC₁ hC I hI).hom.hom.comp ((descVₗ T' hC).hom.hom.comp u)) =
      ξ a ι ((rVₗ hC I).hom.hom.comp ((qC hC I hI).hom.hom.comp u)))
    (hρ : ρ = eqToHom h₁ ≫ (Arr.map a ι (qC₁ hC I hI) (descArr u hom)).hom ≫ eqToHom h₂) :
    ρ ≫ trans a ι (rVₗ hC I) ((qC hC I hI).hom.hom.comp u) ≫ trans a ι (qC hC I hI) u ≫ ζ =
      trans a ι (rV₀ hC I) ((qC hC I hI).hom.hom.comp u) ≫ trans a ι (qC hC I hI) u ≫ ζ := by
  have sq₁ := trans_square (a := a) (ι := ι) _ _ _ _ (qC_rVₗ hC I hI) u h₂.symm
  have sq₀ := trans_square (a := a) (ι := ι) _ _ _ _ (qC_rV₀ hC I hI) u h₁
  have hf := Arr.map_hom_fac (qC₁ hC I hI) (descArr u hom)
  subst hρ
  calc (eqToHom h₁ ≫ (Arr.map a ι (qC₁ hC I hI) (descArr u hom)).hom ≫ eqToHom h₂) ≫
        trans a ι (rVₗ hC I) ((qC hC I hI).hom.hom.comp u) ≫ trans a ι (qC hC I hI) u ≫ ζ
      = eqToHom h₁ ≫ (Arr.map a ι (qC₁ hC I hI) (descArr u hom)).hom ≫ eqToHom h₂ ≫
        (eqToHom h₂.symm ≫ trans a ι (qC₁ hC I hI) ((descVₗ T' hC).hom.hom.comp u) ≫
          trans a ι (descVₗ T' hC) u) ≫ ζ :=
        (Category.assoc _ _ _).trans (congrArg _ ((Category.assoc _ _ _).trans (congrArg _
          (congrArg _ ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ ζ) sq₁))))))
    _ = eqToHom h₁ ≫ ((Arr.map a ι (qC₁ hC I hI) (descArr u hom)).hom ≫
        trans a ι (qC₁ hC I hI) ((descVₗ T' hC).hom.hom.comp u)) ≫
          trans a ι (descVₗ T' hC) u ≫ ζ :=
        congrArg _ ((congrArg _ ((congrArg _ ((Category.assoc _ _ _).trans
          (congrArg _ (Category.assoc _ _ _)))).trans ((eqToHom_trans_assoc _ _ _).trans
            (Category.id_comp _)))).trans (Category.assoc _ _ _).symm)
    _ = eqToHom h₁ ≫ trans a ι (qC₁ hC I hI) ((descV₀ T' hC).hom.hom.comp u) ≫
        (hom ≫ trans a ι (descVₗ T' hC) u ≫ ζ) :=
        congrArg _ ((congrArg (· ≫ _) hf).trans (Category.assoc _ _ _))
    _ = eqToHom h₁ ≫ (trans a ι (qC₁ hC I hI) ((descV₀ T' hC).hom.hom.comp u) ≫
        trans a ι (descV₀ T' hC) u) ≫ ζ :=
        congrArg _ ((congrArg _ hζ).trans (Category.assoc _ _ _).symm)
    _ = _ := ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ζ) sq₀).trans
        (Category.assoc _ _ _))).symm

end Lift

section Main

variable (hA : Cardinal.mk (ringOf B S hS T') < B.cutoff) {C' : Type u} [CommRing C']
  [Algebra (ringOf B S hS T') C'] (hC : Cardinal.mk C' < B.cutoff) (I : Ideal (ringOf B S hS T'))
  (hI : I ^ 2 = ⊥)

include hI in
omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- The extension of the square-zero ideal `I` to `C'` is nilpotent. -/
theorem isNilpotent_map_red : IsNilpotent (I.map (algebraMap (ringOf B S hS T') C')) :=
  ⟨2, by rw [← Ideal.map_pow, hI, Ideal.map_bot]; rfl⟩

/-- The chart data of the lifting problem as a datum along the nerve. -/
noncomputable def chartNerveDatum [Algebra.FormallySmooth (ringOf B S hS T') P.obj]
    {xb : 𝒳.val.obj}
    (ubar : P.obj →ₐ[ringOf B S hS T'] (red I (descNerve T' hC 0)).obj) (c : ξ a ι ubar ⟶ xb)
    [𝒳.val.p.IsHomLift (specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot) c] :
    NerveDatum B.aleph0_lt_cutoff C' hC I hI (stackGroupoid a ι) where
  ubar := ubar
  u₀ := Algebra.FormallySmooth.lift _ (isNilpotent_map_red (C' := C') I hI) ubar
  u₀_lift :=
    AlgHom.ext (Algebra.FormallySmooth.mk_lift _ (isNilpotent_map_red (C' := C') I hI) ubar)
  rbar := chartRbar (hA := hA) hC I ubar c
  src_rbar := rfl
  tgt_rbar := rfl
  norm_rbar := chartRbar_norm hC I ubar c

/-- The square formed by the reduction maps and the maps to the base commutes on spectra. -/
theorem spec_baseMap_q :
    specOverMap (qC hC I hI) ≫ specOverMap (baseMap B.aleph0_lt_cutoff hC hA) =
      specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot ≫
        specOverMap (thk I hI (baseAlg (κ := B.cutoff) hA)).q :=
  (specOverMap_comp _ _).symm.trans ((congrArg specOverMap
    (GroupoidLift.SmallAlg.hom_ext_of_surjective (fun x ↦ ⟨x, rfl⟩) _ _)).trans
      (specOverMap_comp _ _))

/-- The reduced covering `Spec (C' ⧸ I C') ⟶ Spec (A' ⧸ I)` generates a covering sieve. -/
theorem ofArrows_red_mem [Module.FaithfullyFlat (ringOf B S hS T') C']
    [Algebra.FinitePresentation (ringOf B S hS T') C'] :
    Sieve.ofArrows (fun _ : PUnit.{w + 1} ↦ specOver (red I (descNerve T' hC 0)))
      (fun _ ↦ specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot) ∈
        BigFppfOver.topology B S hS (specOver (red I (baseAlg (κ := B.cutoff) hA))) := by
  rw [Sieve.ofArrows, Presieve.ofArrows_pUnit]
  have hFF := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap (ringOf B S hS T') C'))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  have hfp : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap (ringOf B S hS T') C'))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  have hpb := isPullback_SpecMap_of_isPushout _ _ _ _
    (isPushout_red B.aleph0_lt_cutoff C' hC I hI hA)
  exact Space.sieve_generate_singleton_mem_topology_over_of_flat B S hS _
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb hFF.2)
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb hFF.1)
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb hfp)

/-- **The lifting step for a stack from a chart point over a covering.** Let `C'` be a faithfully
flat finitely presented `A'`-algebra and `I ⊆ A'` a square-zero ideal. If an object `x̄` of `𝒳`
over `Spec (A' ⧸ I)` receives a morphism `c : ξ ū ⟶ x̄` over `Spec (C' ⧸ I C') ⟶ Spec (A' ⧸ I)`
from the object of a chart point at which the arrows have a formally étale chart, then there are
an object `x'` over `Spec A'`, a point `u : P → C'` with a morphism `ξ u ⟶ x'` over
`Spec C' ⟶ Spec A'`, and a morphism `x̄ ⟶ x'` over `Spec (A' ⧸ I) ⟶ Spec A'`. -/
theorem exists_lift_of_chartPoint
    (h𝒳 : 𝒳.val.p.IsStackInGroupoids.{w} (BigFppfOver.topology B S hS))
    [Module.FaithfullyFlat (ringOf B S hS T') C']
    [Algebra.FinitePresentation (ringOf B S hS T') C']
    [Algebra.FormallySmooth (ringOf B S hS T') P.obj]
    [Module.FinitePresentation P.obj Ω[P.obj⁄ringOf B S hS T']]
    (hG : (stackGroupoid a ι).SrcFormallySmooth)
    {Q : Type u} [CommRing Q] [Algebra (ringOf B S hS T') Q]
    [Module.FinitePresentation Q Ω[Q⁄ringOf B S hS T']]
    (b : Chart (stackArr a ι) Q) (hb : b.IsFormallyEtale) (sV tV : P.obj →ₐ[ringOf B S hS T'] Q)
    (hsV : ∀ (D : SmallAlg (ringOf B S hS T') B.cutoff) (v : Q →ₐ[ringOf B S hS T'] D.obj),
      (b.app D v).src = v.comp sV)
    (htV : ∀ (D : SmallAlg (ringOf B S hS T') B.cutoff) (v : Q →ₐ[ringOf B S hS T'] D.obj),
      (b.app D v).tgt = v.comp tV)
    {xb : 𝒳.val.obj} (hxb : 𝒳.val.p.obj xb = specOver (red I (baseAlg (κ := B.cutoff) hA)))
    (ubar : P.obj →ₐ[ringOf B S hS T'] (red I (descNerve T' hC 0)).obj) (c : ξ a ι ubar ⟶ xb)
    (hc : 𝒳.val.p.IsHomLift (specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot) c)
    (εbar : Q →ₐ[ringOf B S hS T'] (red I (descNerve T' hC 0)).obj)
    (hε : b.app _ εbar = Arr.idt ubar) :
    ∃ (u : P.obj →ₐ[ringOf B S hS T'] (descNerve T' hC 0).obj) (x' : 𝒳.val.obj)
      (ζ : ξ a ι u ⟶ x') (φ : xb ⟶ x'),
      𝒳.val.p.IsHomLift (specOverMap (baseMap B.aleph0_lt_cutoff hC hA)) ζ ∧
        𝒳.val.p.IsHomLift (specOverMap (thk I hI (baseAlg (κ := B.cutoff) hA)).q) φ := by
  have := hc
  let D := chartNerveDatum hA hC I hI ubar c
  have hcoc : D.IsCocycle := chartRbar_cocycle hC I ubar c
  obtain ⟨ε₀, ⟨hε₀, -⟩, -⟩ := hb _ _ (thk I hI (descNerve T' hC 0)).q
    (thk I hI (descNerve T' hC 0)).surj (thk I hI (descNerve T' hC 0)).sq εbar (Arr.idt D.u₀)
    ((Arr.map_idt _ _).trans ((congrArg Arr.idt D.u₀_lift).trans hε.symm))
  obtain ⟨u, hu, r, hrq, hs, ht, hcocy⟩ := NerveDatum.exists_lift_arrow_cocycle (D := D)
    (sV := sV) (tV := tV) (εbar := εbar) (hsV := hsV) (htV := htV) (hε := hε) (hb := hb)
    (ε₀ := ε₀) (hε₀ := hε₀) hG hcoc
  obtain ⟨src, tgt, hom, lift⟩ := r
  change src = _ at hs
  change tgt = _ at ht
  subst hs ht
  change (qC hC I hI).hom.hom.comp u = ubar at hu
  subst hu
  obtain ⟨_, hcocy⟩ := hcocy
  obtain ⟨x', ζ, hζl, hζ⟩ := exists_descent_of_hom hA u hom h𝒳 hcocy
  have hx' : 𝒳.val.p.obj x' = specOver (baseAlg (κ := B.cutoff) hA) :=
    @IsHomLift.codomain_eq _ _ _ _ 𝒳.val.p _ _ _ _
      (specOverMap (baseMap B.aleph0_lt_cutoff hC hA)) ζ hζl
  have := hζl
  have hζ' : 𝒳.val.p.IsHomLift (specOverMap (baseThk B.aleph0_lt_cutoff hC hI hA).bot ≫
      specOverMap (thk I hI (baseAlg (κ := B.cutoff) hA)).q) (trans a ι (qC hC I hI) u ≫ ζ) :=
    isHomLift_of_eq (spec_baseMap_q hA hC I hI) inferInstance
  obtain ⟨φ, hφ, -⟩ := exists_hom_of_chart (baseThk B.aleph0_lt_cutoff hC hI hA).bot (rV₀ hC I)
    (rVₗ hC I) h𝒳 (isPullback_specOverMap_of_isPushout _ _ _ _
      (isPushout_red_nerve_one B.aleph0_lt_cutoff C' hC I hI hA)) (ofArrows_red_mem hA hC I hI)
    (specOverMap (thk I hI (baseAlg (κ := B.cutoff) hA)).q) hxb hx' _ c hc
    (trans a ι (qC hC I hI) u ≫ ζ) hζ' (chartRbar hC I _ c).hom (chartRbar hC I _ c).lift
    (chartRbar_fac hC I _ c) (red_descArr_fac u hom ζ hζ _ _ _ (Arr.hom_eq_of_eq hrq.symm))
  exact ⟨u, x', ζ, φ, hζl, hφ⟩

end Main

end StackChart

end AlgebraicGeometry.Stack.GroupoidLift

end
