module

public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianFlatAffineSiteKernel

/-!
# Extensions of cartesian modules

Let `R` be a presheaf of commutative rings on a category `D`. A presheaf of `R`-modules `P` is
cartesian over a morphism `f : X ⟶ Y` when the base change map `R(Y) ⊗_{R(X)} P(X) ⟶ P(Y)` is an
isomorphism. This file proves that the middle term of a sequence `0 ⟶ K ⟶ E ⟶ G ⟶ 0` of
presheaves of `R`-modules which is exact on sections is cartesian over `f` when `K` and `G` are,
and constructs the pullback of a morphism `g : E ⟶ G` along the map `𝒪 ⟶ G` given by a
compatible family of sections of `G`.

## Main definitions

* `Stacks.PresheafOfModules.liftPresheaf`: the pullback of `g : E ⟶ G` along the map `𝒪 ⟶ G`
  given by a compatible family of sections `σ` of `G`.
* `Stacks.PresheafOfModules.liftProj`: the projection of this pullback to `𝒪`.
* `Stacks.PresheafOfModules.liftIncl`: the inclusion into this pullback of a module mapped to zero
  by `g`.

## Main results

* `Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_split`: a split extension of `𝒪` by a
  cartesian module is cartesian.
* `Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_shortExact`: the middle term of a
  sequence `0 ⟶ K ⟶ E ⟶ G ⟶ 0`, exact on sections, with cartesian outer terms is cartesian.

## References

* [Stacks Project, Tag 07B4](https://stacks.math.columbia.edu/tag/07B4)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

open scoped ChangeOfRings

universe w m u u₁ v₁ r u' v'

namespace Stacks.PresheafOfModules

variable {D : Type u'} [Category.{v'} D] {R : Dᵒᵖ ⥤ CommRingCat.{r}}

/-- The base change maps are natural in the module: `θ_N ∘ (1 ⊗ φ_X) = φ_Y ∘ θ_M`. -/
private theorem restrictionBaseChange_lTensor_app
    {M N : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat)} (φ : M ⟶ N)
    {X Y : Dᵒᵖ} (f : X ⟶ Y) :
    letI : Algebra (R.obj X) (R.obj Y) := (R.map f).hom.toAlgebra
    letI θM : TensorProduct (R.obj X) (R.obj Y) (M.obj X) →ₗ[R.obj Y] M.obj Y :=
      (restrictionBaseChange M f).hom
    letI θN : TensorProduct (R.obj X) (R.obj Y) (N.obj X) →ₗ[R.obj Y] N.obj Y :=
      (restrictionBaseChange N f).hom
    letI φX : M.obj X →ₗ[R.obj X] N.obj X := (φ.app X).hom
    ∀ z, θN (φX.lTensor (R.obj Y) z) = φ.app Y (θM z) := by
  let : Algebra (R.obj X) (R.obj Y) := (R.map f).hom.toAlgebra
  intro z
  induction z using TensorProduct.induction_on with
  | zero => erw [map_zero, map_zero]
  | add z z' hz hz' => erw [map_add, map_add, map_add, map_add, hz, hz']
  | tmul b k =>
    rw [LinearMap.lTensor_tmul]
    change restrictionBaseChange N f (b ⊗ₜ[R.obj X, (R.map f).hom] φ.app X k) =
      φ.app Y (restrictionBaseChange M f (b ⊗ₜ[R.obj X, (R.map f).hom] k))
    rw [restrictionBaseChange_tmul, restrictionBaseChange_tmul,
      ← PresheafOfModules.naturality_apply]
    exact ((φ.app Y).hom.map_smul b (M.map f k)).symm

/-- **A split extension of `𝒪` by a cartesian module is cartesian.** Let `ι : K ⟶ P` be
injective on sections with image the kernel of a natural projection `π : P ⟶ 𝒪`, and let `ε` be
a section over `X` with `π ε = 1`. If `K` is cartesian over `f : X ⟶ Y`, so is `P`. -/
theorem isIso_restrictionBaseChange_of_split
    {K P : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat)} (ι : K ⟶ P)
    (π : ∀ Z, P.obj Z →ₗ[R.obj Z] R.obj Z)
    (hπ : ∀ ⦃Z Z' : Dᵒᵖ⦄ (f : Z ⟶ Z') (p : P.obj Z), π Z' (P.map f p) = R.map f (π Z p))
    (hι : ∀ Z, Function.Injective (ι.app Z)) (hπι : ∀ Z k, π Z (ι.app Z k) = 0)
    (hex : ∀ Z (p : P.obj Z), π Z p = 0 → ∃ k, ι.app Z k = p)
    {X Y : Dᵒᵖ} (f : X ⟶ Y) (ε : P.obj X) (hε : π X ε = 1)
    (hK : IsIso (restrictionBaseChange K f)) : IsIso (restrictionBaseChange P f) := by
  let : Algebra (R.obj X) (R.obj Y) := (R.map f).hom.toAlgebra
  let θK : TensorProduct (R.obj X) (R.obj Y) (K.obj X) →ₗ[R.obj Y] K.obj Y :=
    (restrictionBaseChange K f).hom
  let θ : TensorProduct (R.obj X) (R.obj Y) (P.obj X) →ₗ[R.obj Y] P.obj Y :=
    (restrictionBaseChange P f).hom
  let ιX : K.obj X →ₗ[R.obj X] P.obj X := (ι.app X).hom
  have hKb : Function.Bijective θK := (ConcreteCategory.isIso_iff_bijective _).mp hK
  have nι : ∀ z, θ (ιX.lTensor (R.obj Y) z) = ι.app Y (θK z) :=
    restrictionBaseChange_lTensor_app ι f
  set εY : P.obj Y := P.map f ε with hεY
  have hεY' : π Y εY = 1 := by rw [hπ, hε, map_one]
  have hθε : ∀ b : R.obj Y, θ (b ⊗ₜ ε) = b • εY := fun b => restrictionBaseChange_tmul P f b ε
  have hdec : ∀ Z (e : P.obj Z) (p : P.obj Z), π Z e = 1 →
      ∃ k, p = ι.app Z k + π Z p • e := by
    intro Z e p he
    obtain ⟨k, hk⟩ := hex Z (p - π Z p • e) (by rw [map_sub, map_smul, he, smul_eq_mul,
      mul_one, sub_self])
    exact ⟨k, by rw [hk, sub_add_cancel]⟩
  have hz : ∀ z : TensorProduct (R.obj X) (R.obj Y) (P.obj X),
      ∃ (zK : TensorProduct (R.obj X) (R.obj Y) (K.obj X)) (b : R.obj Y),
        z = ιX.lTensor (R.obj Y) zK + b ⊗ₜ ε := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | add z z' hz hz' =>
      obtain ⟨zK, b, rfl⟩ := hz
      obtain ⟨zK', b', rfl⟩ := hz'
      exact ⟨zK + zK', b + b', by rw [map_add, TensorProduct.add_tmul]; abel⟩
    | tmul b p =>
      obtain ⟨k, hk⟩ := hdec X ε p hε
      refine ⟨b ⊗ₜ k, π X p • b, ?_⟩
      rw [LinearMap.lTensor_tmul]
      conv_lhs => rw [hk]
      rw [TensorProduct.tmul_add, ← TensorProduct.smul_tmul]
  have hπθ : ∀ (zK : TensorProduct (R.obj X) (R.obj Y) (K.obj X)) (b : R.obj Y),
      π Y (θ (ιX.lTensor (R.obj Y) zK + b ⊗ₜ ε)) = b := by
    intro zK b
    rw [map_add, nι, hθε, map_add, hπι, map_smul, hεY', smul_eq_mul, mul_one, zero_add]
  rw [ConcreteCategory.isIso_iff_bijective]
  show Function.Bijective θ
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz0
    obtain ⟨zK, b, rfl⟩ := hz z
    have hb : b = 0 := by rw [← hπθ zK b, hz0, map_zero]
    subst hb
    rw [TensorProduct.zero_tmul, add_zero] at hz0 ⊢
    rw [nι] at hz0
    have h1 : θK zK = 0 := hι Y (by rw [hz0, map_zero])
    have h2 : zK = 0 := hKb.1 (by rw [h1, map_zero])
    rw [h2, map_zero]
  · intro q
    obtain ⟨k, hk⟩ := hdec Y εY q hεY'
    obtain ⟨zK, hzK⟩ := hKb.2 k
    refine ⟨ιX.lTensor (R.obj Y) zK + π Y q ⊗ₜ ε, ?_⟩
    rw [map_add, nι, hθε, hzK, ← hk]

/-- **The middle term of an extension of cartesian modules is cartesian**, as soon as the
sequence `0 ⟶ K ⟶ E ⟶ G ⟶ 0` is exact on sections. -/
theorem isIso_restrictionBaseChange_of_shortExact
    {K E G : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat)}
    (ι : K ⟶ E) (φ : E ⟶ G) (hι : ∀ Z, Function.Injective (ι.app Z))
    (hex : ∀ Z, Function.Exact (ι.app Z) (φ.app Z)) (hφ : ∀ Z, Function.Surjective (φ.app Z))
    {X Y : Dᵒᵖ} (f : X ⟶ Y) (hK : IsIso (restrictionBaseChange K f))
    (hG : IsIso (restrictionBaseChange G f)) : IsIso (restrictionBaseChange E f) := by
  let : Algebra (R.obj X) (R.obj Y) := (R.map f).hom.toAlgebra
  let θK : TensorProduct (R.obj X) (R.obj Y) (K.obj X) →ₗ[R.obj Y] K.obj Y :=
    (restrictionBaseChange K f).hom
  let θ : TensorProduct (R.obj X) (R.obj Y) (E.obj X) →ₗ[R.obj Y] E.obj Y :=
    (restrictionBaseChange E f).hom
  let θG : TensorProduct (R.obj X) (R.obj Y) (G.obj X) →ₗ[R.obj Y] G.obj Y :=
    (restrictionBaseChange G f).hom
  let ιX : K.obj X →ₗ[R.obj X] E.obj X := (ι.app X).hom
  let φX : E.obj X →ₗ[R.obj X] G.obj X := (φ.app X).hom
  have hKb : Function.Bijective θK := (ConcreteCategory.isIso_iff_bijective _).mp hK
  have hGb : Function.Bijective θG := (ConcreteCategory.isIso_iff_bijective _).mp hG
  have nι : ∀ z, θ (ιX.lTensor (R.obj Y) z) = ι.app Y (θK z) :=
    restrictionBaseChange_lTensor_app ι f
  have nφ : ∀ z, θG (φX.lTensor (R.obj Y) z) = φ.app Y (θ z) :=
    restrictionBaseChange_lTensor_app φ f
  have hexX : Function.Exact ιX φX := hex X
  have hlex : Function.Exact (ιX.lTensor (R.obj Y)) (φX.lTensor (R.obj Y)) :=
    lTensor_exact (R.obj Y) hexX (hφ X)
  have hlsurj : Function.Surjective (φX.lTensor (R.obj Y)) :=
    LinearMap.lTensor_surjective (R.obj Y) (hφ X)
  rw [ConcreteCategory.isIso_iff_bijective]
  show Function.Bijective θ
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz0
    have h1 : φX.lTensor (R.obj Y) z = 0 := hGb.1 (by
      rw [nφ, show θ z = 0 from hz0, map_zero, map_zero])
    obtain ⟨w, rfl⟩ := (hlex z).mp h1
    have h2 : θK w = 0 := hι Y (by rw [← nι, hz0, map_zero])
    rw [hKb.1 (show θK w = θK 0 by rw [h2, map_zero]), map_zero]
  · intro e
    obtain ⟨t, ht⟩ := hGb.2 (φ.app Y e)
    obtain ⟨t', rfl⟩ := hlsurj t
    obtain ⟨k, hk⟩ := ((hex Y) (e - θ t')).mp (by
      rw [map_sub, sub_eq_zero, ← ht, ← nφ])
    obtain ⟨w, hw⟩ := hKb.2 k
    refine ⟨t' + ιX.lTensor (R.obj Y) w, ?_⟩
    rw [map_add, nι, hw, hk, add_sub_cancel]

section Lift

variable {E G : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat)} (g : E ⟶ G)
  (σ : ∀ Z, G.obj Z) (hσ : ∀ ⦃Z Z' : Dᵒᵖ⦄ (f : Z ⟶ Z'), G.map f (σ Z) = σ Z')

/-- The pairs `(e, a)` of a section of `E` and a section of `𝒪` over `Z` with `g e = a • σ`: the
sections over `Z` of the pullback of `g` along the map `𝒪 ⟶ G` given by the family `σ`. -/
def liftSubmodule (Z : Dᵒᵖ) : Submodule (R.obj Z) (E.obj Z × R.obj Z) where
  carrier := {p | g.app Z p.1 = p.2 • σ Z}
  add_mem' {p q} hp hq := by
    simp only [Set.mem_setOf_eq] at hp hq ⊢
    rw [Prod.fst_add, Prod.snd_add, map_add, hp, hq, add_smul]
  zero_mem' := by
    simp only [Set.mem_setOf_eq, Prod.fst_zero, Prod.snd_zero, map_zero, zero_smul]
  smul_mem' c p hp := by
    simp only [Set.mem_setOf_eq] at hp ⊢
    rw [Prod.smul_fst, Prod.smul_snd, map_smul, hp, smul_smul, smul_eq_mul]

include hσ in
/-- The restriction along `f : Z ⟶ Z'` of an element of `liftSubmodule g σ Z` lies in
`liftSubmodule g σ Z'`. -/
theorem liftSubmodule_map {Z Z' : Dᵒᵖ} (f : Z ⟶ Z') (p : liftSubmodule g σ Z) :
    (E.map f p.1.1, R.map f p.1.2) ∈ liftSubmodule g σ Z' := by
  show g.app Z' (E.map f p.1.1) = (R.map f p.1.2) • σ Z'
  rw [PresheafOfModules.naturality_apply, show g.app Z p.1.1 = p.1.2 • σ Z from p.2,
    PresheafOfModules.map_smul, hσ]
  rfl

/-- The pullback of `g` along `σ`, as a presheaf of abelian groups. -/
noncomputable def liftAb : Dᵒᵖ ⥤ AddCommGrpCat.{max m r} where
  obj Z := AddCommGrpCat.of (liftSubmodule g σ Z)
  map {Z Z'} f := AddCommGrpCat.ofHom
    { toFun := fun p => ⟨(E.map f p.1.1, R.map f p.1.2), liftSubmodule_map g σ hσ f p⟩
      map_zero' := Subtype.ext (Prod.ext (map_zero _) (map_zero _))
      map_add' := fun p q => Subtype.ext (Prod.ext (map_add _ _ _) (map_add _ _ _)) }
  map_id Z := AddCommGrpCat.ext fun p => Subtype.ext (Prod.ext (by simp; rfl) (by simp))
  map_comp f f' := AddCommGrpCat.ext fun p => Subtype.ext (Prod.ext (by simp; rfl) (by simp))

/-- The module structure on the sections of `liftAb g σ hσ`. -/
noncomputable instance (Z : Dᵒᵖ) :
    Module ((R ⋙ forget₂ CommRingCat RingCat).obj Z) ((liftAb g σ hσ).obj Z) :=
  inferInstanceAs (Module (R.obj Z) (liftSubmodule g σ Z))

/-- **The pullback of `g` along `σ`**, as a presheaf of modules. -/
noncomputable def liftPresheaf : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat) :=
  PresheafOfModules.ofPresheaf (liftAb g σ hσ) (fun _ _ f c p =>
    Subtype.ext (Prod.ext (PresheafOfModules.map_smul E f c p.1.1) (map_mul _ _ _)))

/-- The projection of the pullback to `𝒪`. -/
def liftProj (Z : Dᵒᵖ) : (liftPresheaf g σ hσ).obj Z →ₗ[R.obj Z] R.obj Z where
  toFun p := (p : liftSubmodule g σ Z).1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The inclusion of a module mapped to zero by `g` into the pullback. -/
noncomputable def liftIncl {F : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat)}
    (k : F ⟶ E) (hk : ∀ Z x, g.app Z (k.app Z x) = 0) : F ⟶ liftPresheaf g σ hσ :=
  PresheafOfModules.homMk
    { app Z := AddCommGrpCat.ofHom
        { toFun := fun x => (⟨(k.app Z x, 0), by
            change g.app Z (k.app Z x) = (0 : R.obj Z) • σ Z
            rw [zero_smul, hk]⟩ : liftSubmodule g σ Z)
          map_zero' := Subtype.ext (Prod.ext (map_zero _) rfl)
          map_add' := fun x y => Subtype.ext (Prod.ext (map_add _ _ _) (add_zero 0).symm) }
      naturality {Z Z'} f := AddCommGrpCat.ext fun x => Subtype.ext <|
        Prod.ext (PresheafOfModules.naturality_apply k f x) (map_zero _).symm }
    (fun Z c x => Subtype.ext (Prod.ext ((k.app Z).hom.map_smul c x) (mul_zero c).symm))

end Lift

end Stacks.PresheafOfModules

end
