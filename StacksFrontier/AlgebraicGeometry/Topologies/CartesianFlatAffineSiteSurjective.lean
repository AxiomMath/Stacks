module

public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianFlatAffineSiteExtension

/-!
# Epimorphisms with cartesian kernel are surjective on the sections over an affine object

Let `C` be a site of affine schemes with fibre products along its coverings, as in
`StacksFrontier.AlgebraicGeometry.Topologies.CartesianFlatAffineSite`, and let `φ : E ⟶ G` be a map of
sheaves of modules which is locally surjective and whose kernel `F ⟶ E` is cartesian. This file
proves that `φ` is surjective on the sections over every object.

## Main results

* `Stacks.PresheafOfModules.surjective_of_faithfullyFlat_family`: a natural map `P ⟶ 𝒪` of
  presheaves of modules is surjective at `X` if it is surjective at the members of a finite
  faithfully flat family over `X` over which `P` is cartesian.
* `Stacks.PresheafOfModules.isSheaf_liftPresheaf`: the pullback of a map of sheaves along a
  compatible family of sections is a sheaf.
* `Stacks.FlatAffineSite.surjective_app_of_isLocallySurjective`: a locally surjective map of
  sheaves of modules with cartesian kernel is surjective on the sections over every object.

## References

* [Stacks Project, Tag 07B4](https://stacks.math.columbia.edu/tag/07B4)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

open scoped ChangeOfRings TensorProduct

universe w m u u₁ v₁ r u' v'

namespace Stacks.PresheafOfModules

variable {D : Type u'} [Category.{v'} D] {R : Dᵒᵖ ⥤ CommRingCat.{r}}

/-- **Surjectivity of a natural map to `𝒪` descends along a faithfully flat family over which
the source is cartesian.** Let `π : P ⟶ 𝒪` be natural and let `q i : W i ⟶ X` be a finite family
such that `R X → ∏ i, R (W i)` is faithfully flat and `P` is cartesian over each `q i`. If each
`π (W i)` is surjective, then so is `π X`. -/
theorem surjective_of_faithfullyFlat_family
    {P : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat)}
    (π : ∀ Z, P.obj Z →ₗ[R.obj Z] R.obj Z)
    (hπ : ∀ ⦃Z Z' : Dᵒᵖ⦄ (f : Z ⟶ Z') (p : P.obj Z), π Z' (P.map f p) = R.map f (π Z p))
    {X : D} {I : Type*} [Finite I] (W : I → D) (q : ∀ i, W i ⟶ X)
    (hff : (RingHom.pi (fun i => (R.map (q i).op).hom)).FaithfullyFlat)
    (hq : ∀ i, IsIso (restrictionBaseChange P (q i).op))
    (hs : ∀ i, Function.Surjective (π (op (W i)))) :
    Function.Surjective (π (op X)) := by
  classical
  let _ := Fintype.ofFinite I
  let alg : ∀ i, Algebra (R.obj (op X)) (R.obj (op (W i))) :=
    fun i => (R.map (q i).op).hom.toAlgebra
  let : Module.FaithfullyFlat (R.obj (op X)) (∀ i, R.obj (op (W i))) := hff
  let A := R.obj (op X)
  let πX : P.obj (op X) →ₗ[A] A := π (op X)
  have hk : ∀ i, Function.Surjective (πX.lTensor (R.obj (op (W i)))) := by
    intro i
    let θ : TensorProduct A (R.obj (op (W i))) (P.obj (op X)) →ₗ[R.obj (op (W i))]
        P.obj (op (W i)) := (restrictionBaseChange P (q i).op).hom
    have hθ : Function.Bijective θ :=
      (ConcreteCategory.isIso_iff_bijective _).mp (hq i)
    let ρ : TensorProduct A (R.obj (op (W i))) A ≃ₗ[A] R.obj (op (W i)) :=
      TensorProduct.rid A (R.obj (op (W i)))
    have hsq : ∀ z, ρ (πX.lTensor (R.obj (op (W i))) z) = π (op (W i)) (θ z) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add z z' hz hz' => simp only [map_add, hz, hz']
      | tmul b p =>
        rw [LinearMap.lTensor_tmul]
        show ρ (b ⊗ₜ πX p) = π (op (W i)) (restrictionBaseChange P (q i).op
          (b ⊗ₜ[R.obj (op X), (R.map (q i).op).hom] p))
        rw [restrictionBaseChange_tmul]
        refine Eq.trans ?_ ((π (op (W i))).map_smul b ((P.map (q i).op) p)).symm
        rw [hπ, TensorProduct.rid_tmul, smul_eq_mul, Algebra.smul_def, mul_comm]
        rfl
    intro y
    obtain ⟨p, hp⟩ := hs i (ρ y)
    obtain ⟨z, rfl⟩ := hθ.2 p
    refine ⟨z, ρ.injective ?_⟩
    rw [hsq, hp]
  have hprod : Function.Surjective (πX.lTensor (∀ i, R.obj (op (W i)))) := by
    let e₁ : ((∀ i, R.obj (op (W i))) ⊗[A] P.obj (op X)) ≃ₗ[A]
        ∀ i, R.obj (op (W i)) ⊗[A] P.obj (op X) :=
      TensorProduct.piLeft A (P.obj (op X)) (fun i => (R.obj (op (W i)) : Type r))
    let e₂ : ((∀ i, R.obj (op (W i))) ⊗[A] A) ≃ₗ[A] ∀ i, R.obj (op (W i)) ⊗[A] A :=
      TensorProduct.piLeft A A (fun i => (R.obj (op (W i)) : Type r))
    have hsq : ∀ (x : (∀ i, R.obj (op (W i))) ⊗[A] P.obj (op X)) (i : I),
        e₂ (πX.lTensor (∀ i, R.obj (op (W i))) x) i = πX.lTensor (R.obj (op (W i))) (e₁ x i) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => intro i; simp
      | add x y hx hy =>
        intro i
        simp only [map_add, Pi.add_apply, hx i, hy i]
      | tmul c z =>
        intro i
        simp [e₁, e₂]
    intro y
    choose z hz using fun i => hk i (e₂ y i)
    obtain ⟨x, hx⟩ := e₁.surjective z
    refine ⟨x, e₂.injective (funext fun i => ?_)⟩
    rw [hsq, hx, hz]
  exact (Module.FaithfullyFlat.lTensor_surjective_iff_surjective A (∀ i, R.obj (op (W i)))
    πX).mp hprod

section Lift

variable {E G : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat)} (g : E ⟶ G)
  (σ : ∀ Z, G.obj Z) (hσ : ∀ ⦃Z Z' : Dᵒᵖ⦄ (f : Z ⟶ Z'), G.map f (σ Z) = σ Z')

/-- A section of the pullback presheaf, read as a pair. -/
private def liftElem {Z : Dᵒᵖ}
    (p : ((liftPresheaf g σ hσ).presheaf ⋙ forget AddCommGrpCat.{max m r}).obj Z) :
    liftSubmodule g σ Z := p

/-- The forgetful functor sends a sheaf of abelian groups to a sheaf of types. -/
private theorem isSheaf_forget_of_isSheaf {J : GrothendieckTopology D} {A : Dᵒᵖ ⥤ AddCommGrpCat.{w}}
    (h : Presheaf.IsSheaf J A) : Presieve.IsSheaf J (A ⋙ forget AddCommGrpCat.{w}) :=
  (isSheaf_iff_isSheaf_of_type _ _).mp (Presheaf.isSheaf_comp_of_isSheaf J _ _ h)

/-- A natural projection of a compatible family into a sheaf of types has a unique amalgamation
compatible with the projection. -/
private theorem exists_amalgamation_of_proj {J : GrothendieckTopology D} {T F : Dᵒᵖ ⥤ Type*}
    (hF : Presieve.IsSheaf J F) (p : ∀ Z, T.obj Z → F.obj Z)
    (hp : ∀ ⦃Z Z' : Dᵒᵖ⦄ (f : Z ⟶ Z') (t : T.obj Z), p Z' (T.map f t) = F.map f (p Z t))
    {X : D} {S : Sieve X} (hS : S ∈ J X) {x : Presieve.FamilyOfElements T S.arrows}
    (hx : x.Compatible) :
    ∃ e : F.obj (op X), (∀ ⦃Y⦄ (f : Y ⟶ X) (hf : S f), F.map f.op e = p _ (x f hf)) ∧
      ∀ t : T.obj (op X), (∀ ⦃Y⦄ (f : Y ⟶ X) (hf : S f), T.map f.op t = x f hf) → p _ t = e := by
  let xp : Presieve.FamilyOfElements F S.arrows := fun Y f hf => p (op Y) (x f hf)
  have hxp : xp.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
    exact (hp g₁.op _).symm.trans ((congrArg (p _) (hx g₁ g₂ h₁ h₂ w)).trans (hp g₂.op _))
  refine ⟨(hF S hS).amalgamate _ hxp, fun Y f hf => (hF S hS).valid_glue hxp f hf,
    fun t ht => (hF S hS).isSeparatedFor.ext fun Y f hf => ?_⟩
  rw [← hp, ht f hf, (hF S hS).valid_glue hxp f hf]

/-- **The pullback of a map of sheaves of modules along a compatible family of sections is a
sheaf** when `E`, `G` and the structure sheaf are sheaves. -/
theorem isSheaf_liftPresheaf {J : GrothendieckTopology D} (hE : Presheaf.IsSheaf J E.presheaf)
    (hG : Presheaf.IsSheaf J G.presheaf)
    (hR : Presheaf.IsSheaf J (PresheafOfModules.unit (R ⋙ forget₂ CommRingCat RingCat)).presheaf) :
    Presheaf.IsSheaf J (liftPresheaf g σ hσ).presheaf := by
  apply Presheaf.isSheaf_of_isSheaf_comp J _ (forget AddCommGrpCat.{max m r})
  rw [isSheaf_iff_isSheaf_of_type]
  have hG' := isSheaf_forget_of_isSheaf hG
  intro X S hS x hx
  obtain ⟨e, he, he'⟩ : ∃ e : E.obj (op X), _ :=
    exists_amalgamation_of_proj (isSheaf_forget_of_isSheaf hE)
    (fun _ t => (liftElem g σ hσ t).1.1) (fun _ _ _ _ => rfl) hS hx
  obtain ⟨a, ha, ha'⟩ : ∃ a : R.obj (op X), _ :=
    exists_amalgamation_of_proj (isSheaf_forget_of_isSheaf hR)
    (fun _ t => (liftElem g σ hσ t).1.2) (fun _ _ _ _ => rfl) hS hx
  have hmem : (e, a) ∈ liftSubmodule g σ (op X) := by
    show g.app (op X) e = a • σ (op X)
    refine (hG' S hS).isSeparatedFor.ext fun Y f hf => ?_
    show G.map f.op (g.app (op X) e) = G.map f.op (a • σ (op X))
    have h1 : g.app (op Y) (E.map f.op e) = (liftElem g σ hσ (x f hf)).1.2 • σ (op Y) :=
      he f hf ▸ (liftElem g σ hσ (x f hf)).2
    rw [← PresheafOfModules.naturality_apply, h1, PresheafOfModules.map_smul, hσ, ← ha f hf]
    rfl
  refine ⟨⟨(e, a), hmem⟩, fun Y f hf => ?_, fun t ht => ?_⟩
  · exact Subtype.ext (Prod.ext (he f hf) (ha f hf))
  · exact Subtype.ext (Prod.ext (he' t ht) (ha' t ht))

end Lift

end Stacks.PresheafOfModules

namespace Stacks.FlatAffineSite

open Stacks.PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {L : C ⥤ Scheme.{u}} {Q : MorphismProperty C}
  {J : GrothendieckTopology C}

/-- **A locally surjective map of sheaves of modules with cartesian kernel is surjective on
sections.** Let `ι : F ⟶ E` and `φ : E ⟶ G` be maps of sheaves of modules on a site of affine
schemes with fibre products along its coverings, with `ι` injective and `ι, φ` exact on every
object, `φ` locally surjective, and `F` cartesian. Then `φ` is surjective on the sections over
every object. -/
theorem surjective_app_of_isLocallySurjective [∀ X, IsAffine (L.obj X)] [Q.HasPullbacks]
    [Q.IsStableUnderBaseChange] [Q.IsStableUnderComposition]
    (hQ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Q f → Flat (L.map f)) (hL : PreservesPullbacksAlong L Q)
    (hJ : HasCoverRefinements.{w} L Q J) (hcov : CoversAreCovering.{w} L Q J)
    (hR : Presheaf.IsSheaf J (rings L ⋙ forget₂ CommRingCat RingCat))
    {F E G : SheafOfModules.{max m u}
      (⟨rings L ⋙ forget₂ CommRingCat RingCat, hR⟩ : Sheaf J RingCat.{u})}
    (ι : F ⟶ E) (φ : E ⟶ G) (hι : ∀ Z, Function.Injective (ι.val.app Z))
    (hex : ∀ Z, Function.Exact (ι.val.app Z) (φ.val.app Z))
    (hF : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), IsIso (restrictionBaseChange F.val f))
    (hφ : ∀ (X : C) (s : G.val.obj (op X)), ∃ S ∈ J X, ∀ ⦃Y : C⦄ (f : Y ⟶ X), S f →
      ∃ t : E.val.obj (op Y), φ.val.app (op Y) t = G.val.map f.op s)
    (X : C) : Function.Surjective (φ.val.app (op X)) := by
  intro s
  obtain ⟨S, hS, hSφ⟩ := hφ X s
  obtain ⟨I, W, r, hr, hrS⟩ := hJ S hS
  have := hr.finite
  choose e he using fun i => hSφ (r i) (hrS i)
  let X₀ : Over X := Over.mk (𝟙 X)
  let W' : I → Over X := fun i => Over.mk (r i)
  let r' : ∀ i, W' i ⟶ X₀ := fun i => Over.homMk (r i) (by simp [W', X₀])
  have hr' : IsCover (Over.forget X ⋙ L) (overProp Q X) r' := ⟨hr.finite, hr.mem, hr.surj⟩
  let Rx := rings (Over.forget X ⋙ L) ⋙ forget₂ CommRingCat RingCat
  let Ex : PresheafOfModules.{max m u} Rx := (E.over X).val
  let Gx : PresheafOfModules.{max m u} Rx := (G.over X).val
  let Fx : PresheafOfModules.{max m u} Rx := (F.over X).val
  let φx : Ex ⟶ Gx := (φ.over X).val
  let ιx : Fx ⟶ Ex := (ι.over X).val
  let σ : ∀ Z : (Over X)ᵒᵖ, Gx.obj Z := fun Z => G.val.map Z.unop.hom.op s
  have hσ : ∀ ⦃Z Z' : (Over X)ᵒᵖ⦄ (f : Z ⟶ Z'), Gx.map f (σ Z) = σ Z' := by
    intro Z Z' f
    show G.val.map f.unop.left.op (G.val.map Z.unop.hom.op s) = G.val.map Z'.unop.hom.op s
    rw [← PresheafOfModules.map_comp_apply, ← op_comp, Over.w]
  let P := liftPresheaf (R := rings (Over.forget X ⋙ L)) φx σ hσ
  have hk : ∀ Z x, φx.app Z (ιx.app Z x) = 0 := fun Z x =>
    (hex (op Z.unop.left)).apply_apply_eq_zero x
  let ι' : Fx ⟶ P :=
    liftIncl (R := rings (Over.forget X ⋙ L)) φx σ hσ ιx hk
  let π : ∀ Z, P.obj Z →ₗ[(rings (Over.forget X ⋙ L)).obj Z] (rings (Over.forget X ⋙ L)).obj Z :=
    fun Z => liftProj (R := rings (Over.forget X ⋙ L)) φx σ hσ Z
  have hπ : ∀ ⦃Z Z' : (Over X)ᵒᵖ⦄ (f : Z ⟶ Z') (p : P.obj Z),
      π Z' (P.map f p) = (rings (Over.forget X ⋙ L)).map f (π Z p) := fun _ _ _ _ => rfl
  have hι' : ∀ Z, Function.Injective (ι'.app Z) := fun Z x y hxy =>
    hι (op Z.unop.left)
      (congrArg (fun p : liftSubmodule (R := rings (Over.forget X ⋙ L)) φx σ Z => p.1.1) hxy)
  have hπι : ∀ Z k, π Z (ι'.app Z k) = 0 := fun _ _ => rfl
  have hexP : ∀ Z (p : P.obj Z), π Z p = 0 → ∃ k, ι'.app Z k = p := by
    intro Z p hp
    let p' : liftSubmodule (R := rings (Over.forget X ⋙ L)) φx σ Z := p
    have hp' : φ.val.app (op Z.unop.left) p'.1.1 = 0 := by
      rw [show φ.val.app (op Z.unop.left) p'.1.1 = p'.1.2 • σ Z from p'.2]
      show p'.1.2 • σ Z = 0
      rw [show p'.1.2 = 0 from hp, zero_smul]
    obtain ⟨k, hk⟩ := ((hex (op Z.unop.left)) _).mp hp'
    exact ⟨k, Subtype.ext (Prod.ext hk hp.symm)⟩
  let ε : ∀ i, P.obj (op (W' i)) := fun i => (⟨(e i, 1), by
    show φ.val.app (op (W i)) (e i) = (1 : (rings L).obj (op (W i))) • σ (op (W' i))
    rw [one_smul, he i]
    rfl⟩ : liftSubmodule (R := rings (Over.forget X ⋙ L)) φx σ (op (W' i)))
  have hε : ∀ i, π _ (ε i) = 1 := fun _ => rfl
  have hsheaf : Presheaf.IsSheaf (J.over X) P.presheaf :=
    isSheaf_liftPresheaf (R := rings (Over.forget X ⋙ L)) _ σ hσ (E.over X).isSheaf
      (G.over X).isSheaf
      (SheafOfModules.unit (Sheaf.over
        (⟨rings L ⋙ forget₂ CommRingCat RingCat, hR⟩ : Sheaf J RingCat.{u}) X)).isSheaf
  have hcart : ∀ (i : I) {Y₁ Y₂ : Over X} (x : Y₁ ⟶ W' i) (y : Y₂ ⟶ W' i) (a : Y₁ ⟶ Y₂),
      a ≫ y = x → IsIso (restrictionBaseChange P a.op) := by
    intro i Y₁ Y₂ x y a _
    refine isIso_restrictionBaseChange_of_split ι' π hπ hι' hπι hexP a.op (P.map y.op (ε i)) ?_
      (hF a.left.op)
    rw [hπ, hε, map_one]
  have hq : ∀ i, IsIso (restrictionBaseChange P (r' i).op) := fun i =>
    isIso_restrictionBaseChange_of_isCover.{w} (Q := overProp Q X) (J := J.over X)
      (fun _ _ f hf => hQ f.left hf) (preservesPullbacksAlong_over X hL)
      (coversAreCovering_over X hcov) P hsheaf hr' hcart (r' i) (hQ _ (hr.mem i))
  have hsurj := surjective_of_faithfullyFlat_family π hπ W' r'
    (faithfullyFlat_rings (Q := overProp Q X) (fun _ _ f hf => hQ f.left hf) hr') hq
    (fun i c => ⟨c • ε i, by rw [map_smul, hε, smul_eq_mul, mul_one]⟩)
  obtain ⟨p, hp⟩ := hsurj 1
  let p' : liftSubmodule (R := rings (Over.forget X ⋙ L)) φx σ (op X₀) := p
  refine ⟨p'.1.1, ?_⟩
  have h := p'.2
  change φ.val.app (op X) _ = p'.1.2 • σ (op X₀) at h
  rw [h, show p'.1.2 = 1 from hp, one_smul]
  show G.val.map (𝟙 X).op s = s
  rw [op_id, PresheafOfModules.map_id]
  rfl

end Stacks.FlatAffineSite

end
