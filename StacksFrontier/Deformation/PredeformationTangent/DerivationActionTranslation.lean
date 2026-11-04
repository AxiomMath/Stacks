module

public import StacksFrontier.Deformation.PredeformationTangent.DerivationMapLinear

/-!
# The action of derivations is translation

For a predeformation category satisfying (S2), twisting a deformation over a
finite-dimensional square-zero extension by a derivation translates its class by the image of
that derivation in the associated tangent vector space.

## Main results

* `Deformation.action_eq_add_gamma` identifies the action with translation by the derivation
  class.

## Implementation notes

The action is presented on the skeleton of a fibre, while the vector-space structure of Tag
06IH is on the associated functor. Both have the same fibrewise isomorphism classes as
underlying set; the statement transports classes across that canonical equality. The
square-zero extension carries the coordinates of `Deformation.squareZeroCoordinates`.

The proof compares the square-zero extension by `V` with the one by `V × V`. A class over
`k[V × V]` whose two projections are the derivation class of `0` and the given class is
twisted by the derivation `(D, 0)`; its three projections along the first, second and sum maps
then exhibit the twisted class as the sum.

## References

* [Stacks Project, Tag 06SU](https://stacks.math.columbia.edu/tag/06SU)
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory

universe uT

/-- Transporting a type equality through the forgetful functor is a cast. -/
theorem eqToHom_types_apply {X Y : Type uT} (h : X = Y) (x : X) :
    ConcreteCategory.hom (eqToHom h : X ⟶ Y) x = cast h x := by
  cases h
  rfl

/-- Casting along `h` and then back along `h.symm` is the identity. -/
theorem cast_symm_cancel_left {α β : Sort uT} (h : α = β) (x : α) :
    cast h.symm (cast h x) = x := by
  cases h
  rfl

/-- Two successive casts along `h` and `h'` are the cast along `h.trans h'`. -/
theorem cast_transitive {α β γ : Sort uT} (h : α = β) (h' : β = γ) (x : α) :
    cast h' (cast h x) = cast (h.trans h') x := by
  cases h
  cases h'
  rfl

end

section
open CategoryTheory

universe u w u₁ v₁

attribute [local instance] derivationMapModuleMulOpposite derivationMapIsCentralScalar
  derivationMapModuleOfAlgebra derivationMapIsScalarTower
  derivationMapIsScalarTowerMulOpposite

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- **Stacks Project, Tag 06SU.** The derivation action on deformations over `k[V]` is
translation by the image of the derivation under the canonical derivation map. -/
@[stacks 06SU "action_translation"]
theorem action_eq_add_gamma
    (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k))
    (h𝓕 : IsPredeformationCategory 𝓕.p)
    (hS2 : SchlessingerConditionS2
      (CategoryOfElements.π (isomorphismClasses 𝓕 h𝓕.cofibered)))
    (V : FGModuleCat.{w} k)
    (A₀ : ArtinianLocalAlgCat.{u, w, w} Λ k)
    (i₀ : A₀ ≃ₐ[Λ] k)
    (hi₀ : ∀ a : A₀, A₀.residueEquiv (IsLocalRing.residue A₀ a) = i₀ a)
    (x₀ : 𝓕.obj) (hx₀ : 𝓕.p.obj x₀ = A₀)
    (hiV : ∀ a : (squareZeroExtensionArtinian.{u, w, w} Λ k).obj V,
      ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj V).residueEquiv
        (IsLocalRing.residue ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj V) a) =
          (TrivSqZeroExt.fstHom Λ k V) (squareZeroCoordinates.{u, w, w} V a))
    (a : DerivationMapAndAction 𝓕.p A₀
      ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj V) i₀
      (squareZeroCoordinates.{u, w, w} V) hi₀ hiV x₀ hx₀)
    (D : Derivation Λ k V)
    (x : Skeleton (𝓕.p.Fiber ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj V))) :
    let L := associatedTangentSpaceModuleStructureUnlifted 𝓕 h𝓕 hS2
    let e : Skeleton (𝓕.p.Fiber ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj V)) ≃
        ((L.functor.obj V : ModuleCat.{u₁} k) : Type u₁) :=
      Equiv.cast (by
        calc
          Skeleton (𝓕.p.Fiber ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj V)) =
              (isomorphismClasses 𝓕 h𝓕.cofibered).obj
                ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj V) :=
            (isomorphismClasses_obj 𝓕 h𝓕.cofibered _).symm
          _ = ((L.functor.obj V : ModuleCat.{u₁} k) : Type u₁) :=
            (congrArg (fun H : FGModuleCat.{w} k ⥤ Type u₁ => H.obj V) L.forget_comp).symm)
    e (a.action D x) = e x + e (a.gamma D) := by
  let L := associatedTangentSpaceModuleStructureUnlifted 𝓕 h𝓕 hS2
  have hW (W : FGModuleCat.{w} k) :
      Skeleton (𝓕.p.Fiber ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj W)) =
        ((L.functor.obj W : ModuleCat.{u₁} k) : Type u₁) :=
    (isomorphismClasses_obj 𝓕 h𝓕.cofibered
      ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj W)).symm.trans
        (congrArg (fun H : FGModuleCat.{w} k ⥤ Type u₁ => H.obj W) L.forget_comp).symm
  change cast (hW V) (a.action D x) = cast (hW V) x + cast (hW V) (a.gamma D)
  have hcls {A : ArtinianLocalAlgCat.{u, w, w} Λ k} {y y' : 𝓕.p.Fiber A}
      (h : classOf 𝓕 h𝓕.cofibered y = classOf 𝓕 h𝓕.cofibered y') :
      toSkeleton y = toSkeleton y' :=
    toSkeleton_eq_toSkeleton_iff.mpr <| Quotient.exact <|
      (classOf_eq 𝓕 h𝓕.cofibered y).symm.trans <|
        (congrArg (cast (isomorphismClasses_obj 𝓕 h𝓕.cofibered A)) h).trans
          (classOf_eq 𝓕 h𝓕.cofibered y')
  have hpair {W W' : FGModuleCat.{w} k} (f : W ⟶ W') (r : k) (m : W) :
      ((squareZeroExtensionArtinian.{u, w, w} Λ k).map f).hom ((r, m) : TrivSqZeroExt k W) =
        ((r, f.hom.hom m) : TrivSqZeroExt k W') := by
    apply TrivSqZeroExt.ext
    · change TrivSqZeroExt.fst (TrivSqZeroExt.map f.hom.hom
        (show TrivSqZeroExt k W from (r, m))) = r
      rw [TrivSqZeroExt.fst_map]
      rfl
    · change TrivSqZeroExt.snd (TrivSqZeroExt.map f.hom.hom
        (show TrivSqZeroExt k W from (r, m))) = f.hom.hom m
      rw [TrivSqZeroExt.snd_map]
      rfl
  have ha0 : a.twistMap 0 = 𝟙 _ := by
    apply ArtinianLocalAlgCat.hom_ext
    ext b
    rcases b with ⟨b₀, b₁⟩
    change (a.twistMap 0).hom ((b₀, b₁) : TrivSqZeroExt k V) = ((b₀, b₁) : TrivSqZeroExt k V)
    rw [a.twistMap_apply_pair]
    exact TrivSqZeroExt.ext rfl (add_zero b₁)
  have hmerge {A B C : ArtinianLocalAlgCat.{u, w, w} Λ k} {F : A ⟶ B} {G : B ⟶ C} {H : A ⟶ C}
      (hH : F ≫ G = H) {x : 𝓕.p.Fiber A} {u u' : 𝓕.p.Fiber B} {y z : 𝓕.p.Fiber C}
      (hu : toSkeleton u = toSkeleton u') (φ : x.1 ⟶ u.1) (φ' : u'.1 ⟶ y.1) (ψ : x.1 ⟶ z.1)
      [𝓕.p.IsHomLift F φ] [𝓕.p.IsHomLift G φ'] [𝓕.p.IsHomLift H ψ] :
      toSkeleton y = toSkeleton z := by
    obtain ⟨j⟩ := toSkeleton_eq_toSkeleton_iff.mp hu
    have : 𝓕.p.IsHomLift (𝟙 B) j.hom.1 := j.hom.2
    have hψ : 𝓕.p.IsHomLift H (φ ≫ j.hom.1 ≫ φ') := by
      have hc : 𝓕.p.IsHomLift (F ≫ 𝟙 _ ≫ G) (φ ≫ j.hom.1 ≫ φ') := inferInstance
      rwa [Category.id_comp, hH] at hc
    exact hcls ((map_classOf 𝓕 h𝓕.cofibered H x y (φ ≫ j.hom.1 ≫ φ')).symm.trans
      (map_classOf 𝓕 h𝓕.cofibered H x z ψ))
  have hbase : a.baseMap 0 ≫ a.twistMap D = a.baseMap D := by
    apply ArtinianLocalAlgCat.hom_ext
    ext b
    rw [← i₀.symm_apply_apply b, ArtinianLocalAlgCat.comp_hom, AlgHom.comp_apply,
      a.baseMap_apply_pair (0 : Derivation Λ k V) (i₀ b),
      show (0 : Derivation Λ k V) (i₀ b) = (0 : V) from rfl,
      a.twistMap_apply_pair D (i₀ b) 0, a.baseMap_apply_pair D (i₀ b)]
    exact TrivSqZeroExt.ext rfl (zero_add (D (i₀ b)))
  have haction0
      (s : Skeleton (𝓕.p.Fiber ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj V))) :
      a.action 0 s = s := by
    obtain ⟨x', y', φ', hx', hφ', hy'⟩ := a.action_pushforward 0 s
    have := IsHomLift.of_fac' 𝓕.p _ φ' x'.2 y'.2 hφ'
    rw [← hy', ← hx']
    refine hcls ((map_classOf 𝓕 h𝓕.cofibered (a.twistMap 0) x' y' φ').symm.trans ?_)
    rw [ha0]
    simp
  have hgamma : a.action D (a.gamma 0) = a.gamma D := by
    obtain ⟨y₀, φ₀, hφ₀, hy₀⟩ := a.gamma_pushforward 0
    obtain ⟨x', y', φ', hx', hφ', hy'⟩ := a.action_pushforward D (a.gamma 0)
    obtain ⟨yD, φD, hφD, hyD⟩ := a.gamma_pushforward D
    have := IsHomLift.of_fac' 𝓕.p _ φ₀ hx₀ y₀.2 hφ₀
    have := IsHomLift.of_fac' 𝓕.p _ φ' x'.2 y'.2 hφ'
    have := IsHomLift.of_fac' 𝓕.p _ φD hx₀ yD.2 hφD
    exact hy'.symm.trans ((hmerge hbase (x := ⟨x₀, hx₀⟩) (hy₀.trans hx'.symm) φ₀ φ' φD).trans hyD)
  have hcastcls (W : FGModuleCat.{w} k)
      (y : 𝓕.p.Fiber ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj W)) :
      cast (hW W) (toSkeleton y) =
        cast (congrArg (fun H : FGModuleCat.{w} k ⥤ Type u₁ => H.obj W) L.forget_comp).symm
          (classOf 𝓕 h𝓕.cofibered y) := by
    have hc := congrArg (fun H : FGModuleCat.{w} k ⥤ Type u₁ => H.obj W) L.forget_comp
    have hy : cast (isomorphismClasses_obj 𝓕 h𝓕.cofibered
        ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj W)).symm (toSkeleton y) =
          classOf 𝓕 h𝓕.cofibered y := by
      have h₁ := cast_symm_cancel_left (isomorphismClasses_obj 𝓕 h𝓕.cofibered
        ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj W)) (classOf 𝓕 h𝓕.cofibered y)
      rwa [classOf_eq] at h₁
    exact (cast_transitive (isomorphismClasses_obj 𝓕 h𝓕.cofibered
      ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj W)).symm hc.symm (toSkeleton y)).symm.trans
        (congrArg (cast hc.symm) hy)
  have hmapsk {W W' : FGModuleCat.{w} k} (f : W ⟶ W')
      (y : 𝓕.p.Fiber ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj W))
      (y' : 𝓕.p.Fiber ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj W')) (φ : y.1 ⟶ y'.1)
      [𝓕.p.IsHomLift ((squareZeroExtensionArtinian.{u, w, w} Λ k).map f) φ] :
      (L.functor.map f).hom (cast (hW W) (toSkeleton y)) = cast (hW W') (toSkeleton y') := by
    rw [hcastcls W y, hcastcls W' y']
    exact (functor_map_cast (R := k) L.forget_comp f (classOf 𝓕 h𝓕.cofibered y)).symm.trans
      (congrArg (cast (congrArg (fun H : FGModuleCat.{w} k ⥤ Type u₁ => H.obj W')
        L.forget_comp).symm)
        (map_classOf 𝓕 h𝓕.cofibered ((squareZeroExtensionArtinian.{u, w, w} Λ k).map f) y y' φ))
  obtain ⟨γ, hγ⟩ := derivationMap_linear 𝓕 h𝓕 A₀ i₀ hi₀ x₀ hx₀ hS2 V hiV a
  have hγzero : cast (hW V) (a.gamma 0) = 0 :=
    ((hγ 0).trans (cast_transitive _ _ _)).symm.trans (map_zero γ)
  let P : FGModuleCat.{w} k := prodFGModule k V V
  let i₂ : V ⟶ P := FGModuleCat.ofHom (LinearMap.inr k (V : Type w) V)
  let p₁ : P ⟶ V := prodFst k V V
  let p₂ : P ⟶ V := prodSnd k V V
  let q : P ⟶ V := FGModuleCat.ofHom
    (LinearMap.coprod (LinearMap.id : V →ₗ[k] V) (LinearMap.id : V →ₗ[k] V))
  obtain ⟨yX, rfl⟩ : ∃ y, toSkeleton y = x := ⟨_, toSkeleton_fromSkeleton_obj x⟩
  obtain ⟨yP, φP, hφP⟩ := exists_fiber_pushforward 𝓕.p h𝓕.cofibered yX
    ((squareZeroExtensionArtinian.{u, w, w} Λ k).map i₂)
  have := IsHomLift.of_fac' 𝓕.p _ φP yX.2 yP.2 hφP
  have hproj (f : P ⟶ V) : (L.functor.map f).hom (cast (hW P) (toSkeleton yP)) =
      (L.functor.map (i₂ ≫ f)).hom (cast (hW V) (toSkeleton yX)) := by
    rw [← hmapsk i₂ yX yP φP, Functor.map_comp]
    rfl
  have hp₁ : (L.functor.map p₁).hom (cast (hW P) (toSkeleton yP)) =
      cast (hW V) (a.gamma 0) := by
    rw [hproj, show i₂ ≫ p₁ = 0 from FGModuleCat.hom_ext (LinearMap.ext fun _ => rfl), hγzero]
    simp
  have hp₂ : (L.functor.map p₂).hom (cast (hW P) (toSkeleton yP)) =
      cast (hW V) (toSkeleton yX) := by
    rw [hproj, show i₂ ≫ p₂ = 𝟙 V from FGModuleCat.hom_ext (LinearMap.ext fun _ => rfl)]
    simp
  have hq : (L.functor.map q).hom (cast (hW P) (toSkeleton yP)) =
      cast (hW V) (toSkeleton yX) := by
    rw [hproj, show i₂ ≫ q = 𝟙 V from FGModuleCat.hom_ext (LinearMap.coprod_inr _ _)]
    simp
  let D₁ : Derivation Λ k P :=
    { toLinearMap := LinearMap.prod (D : k →ₗ[Λ] V) 0
      map_one_eq_zero' := Prod.ext D.map_one_eq_zero rfl
      leibniz' b c := Prod.ext (D.leibniz b c) (by
        change (0 : V) = b • (0 : V) + c • (0 : V)
        simp) }
  let aP := squareZeroDerivationMapAndAction.{u, w, w, u₁, v₁} 𝓕.p h𝓕 A₀ i₀ hi₀ P x₀ hx₀
  have htwist (f : P ⟶ V) (E' : Derivation Λ k V) (hf : ∀ c, f.hom.hom (D₁ c) = E' c) :
      aP.twistMap D₁ ≫ (squareZeroExtensionArtinian.{u, w, w} Λ k).map f =
        (squareZeroExtensionArtinian.{u, w, w} Λ k).map f ≫ a.twistMap E' := by
    apply ArtinianLocalAlgCat.hom_ext
    ext b
    rcases b with ⟨b₀, b₁⟩
    change ((squareZeroExtensionArtinian.{u, w, w} Λ k).map f).hom
        ((aP.twistMap D₁).hom ((b₀, b₁) : TrivSqZeroExt k P)) =
      (a.twistMap E').hom
        (((squareZeroExtensionArtinian.{u, w, w} Λ k).map f).hom ((b₀, b₁) : TrivSqZeroExt k P))
    rw [aP.twistMap_apply_pair, hpair, hpair, a.twistMap_apply_pair]
    apply TrivSqZeroExt.ext
    · rfl
    · change f.hom.hom (b₁ + D₁ b₀) = f.hom.hom b₁ + E' b₀
      rw [map_add, hf]
  have hact {f : P ⟶ V} {E' : Derivation Λ k V}
      (hf : aP.twistMap D₁ ≫ (squareZeroExtensionArtinian.{u, w, w} Λ k).map f =
        (squareZeroExtensionArtinian.{u, w, w} Λ k).map f ≫ a.twistMap E')
      {s : Skeleton (𝓕.p.Fiber ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj P))}
      {s' : Skeleton (𝓕.p.Fiber ((squareZeroExtensionArtinian.{u, w, w} Λ k).obj V))}
      (hs : (L.functor.map f).hom (cast (hW P) s) = cast (hW V) s') :
      (L.functor.map f).hom (cast (hW P) (aP.action D₁ s)) = cast (hW V) (a.action E' s') := by
    obtain ⟨x₁, y₁, φ₁, hx₁, hφ₁, hy₁⟩ := aP.action_pushforward D₁ s
    obtain ⟨x₂, y₂, φ₂, hx₂, hφ₂, hy₂⟩ := a.action_pushforward E' s'
    obtain ⟨w₀, ψ₀, hψ₀⟩ := exists_fiber_pushforward 𝓕.p h𝓕.cofibered x₁
      ((squareZeroExtensionArtinian.{u, w, w} Λ k).map f)
    obtain ⟨w₁, ψ₁, hψ₁⟩ := exists_fiber_pushforward 𝓕.p h𝓕.cofibered y₁
      ((squareZeroExtensionArtinian.{u, w, w} Λ k).map f)
    have := IsHomLift.of_fac' 𝓕.p _ ψ₀ x₁.2 w₀.2 hψ₀
    have := IsHomLift.of_fac' 𝓕.p _ ψ₁ y₁.2 w₁.2 hψ₁
    have := IsHomLift.of_fac' 𝓕.p _ φ₁ x₁.2 y₁.2 hφ₁
    have := IsHomLift.of_fac' 𝓕.p _ φ₂ x₂.2 y₂.2 hφ₂
    have hw₀ : toSkeleton w₀ = toSkeleton x₂ := by
      apply (Equiv.cast (hW V)).injective
      change cast (hW V) _ = cast (hW V) _
      rw [← hmapsk f x₁ w₀ ψ₀, hx₁, hs, hx₂]
    rw [← hy₁, ← hy₂, hmapsk f y₁ w₁ ψ₁]
    exact congrArg (cast (hW V)) (hmerge hf.symm hw₀ ψ₀ φ₂ (φ₁ ≫ ψ₁)).symm
  let zTw := cast (hW P) (aP.action D₁ (toSkeleton yP))
  have k₁ : (L.functor.map p₁).hom zTw = cast (hW V) (a.gamma D) := by
    rw [← hgamma]
    exact hact (htwist p₁ D fun _ => rfl) hp₁
  have k₂ : (L.functor.map p₂).hom zTw = cast (hW V) (toSkeleton yX) := by
    rw [← haction0 (toSkeleton yX)]
    exact hact (htwist p₂ 0 fun _ => rfl) hp₂
  have kq : (L.functor.map q).hom zTw = cast (hW V) (a.action D (toSkeleton yX)) :=
    hact (htwist q D fun _ => add_zero _) hq
  have hq_add : (L.functor.map q).hom = (L.functor.map p₁).hom + (L.functor.map p₂).hom := by
    rw [show q = p₁ + p₂ from FGModuleCat.hom_ext (LinearMap.ext fun _ => rfl)]
    exact congrArg (fun f : L.functor.obj P ⟶ L.functor.obj V => f.hom)
      (L.functor.map_add (f := p₁) (g := p₂))
  rw [← kq, hq_add, LinearMap.add_apply, k₁, k₂, add_comm]

end

end Deformation
