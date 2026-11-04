module

public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# The essential image of the inverse image of sheaves of sets is local

Let `u : C ⥤ D` be a continuous functor between sites `(C, J)` and `(D, K)`, and let
`u⁻¹ ⊣ u_*` be the inverse and direct image of sheaves of sets. Suppose that the unit
`ℱ ⟶ u_* u⁻¹ ℱ` is an isomorphism, so that `u⁻¹` is fully faithful. This file gives a criterion,
in terms of sections, for a sheaf of sets `𝒬` on `D` to lie in the essential image of `u⁻¹`:

* every section of `𝒬` is, locally, the restriction of a section of `𝒬` over an object `u W` of
  the image of `u`, compatibly with any given morphism to an object of the image of `u`;
* two sections of `𝒬` over `u W` which agree after restriction to some `V ⟶ u W` agree, locally
  on `V`, after restriction to some `u W' ⟶ u W` with `W' ⟶ W` in `C`.

This is `CategoryTheory.Presheaf.IsLocallyFromImage`. Every sheaf of the form `u⁻¹ ℱ` satisfies
it when `u⁻¹` is computed by the sheafified left Kan extension along a representably flat `u`
(`CategoryTheory.Presheaf.isLocallyFromImage_sheafPullback`), the property is local on `C`
(`CategoryTheory.Presheaf.IsLocallyFromImage.of_locallyIso`), and it implies that the counit
`u⁻¹ u_* 𝒬 ⟶ 𝒬` is an isomorphism (`CategoryTheory.Presheaf.isIso_counit_of_isLocallyFromImage`).
Together: a sheaf of sets on `D` which is, locally on `C`, isomorphic to the inverse image of a
sheaf of sets on `C` lies in the essential image of `u⁻¹`.

## Main definitions

* `CategoryTheory.Presheaf.IsLocallyFromImage`: the criterion above.

## Main results

* `CategoryTheory.Presheaf.isIso_counit_of_isLocallyFromImage`: the criterion makes the counit an
  isomorphism.
* `CategoryTheory.Presheaf.isLocallyFromImage_sheafPullback`: inverse images satisfy the criterion.
* `CategoryTheory.Presheaf.IsLocallyFromImage.of_locallyIso`: the criterion is local on `C`.

## Implementation notes

The counit is bijective on sections over the objects `u W`, by a triangle identity, since the unit
is invertible. The two halves of the criterion upgrade this to local surjectivity and local
injectivity of the counit, using for local injectivity that the inverse image itself satisfies the
first half of the criterion. For the inverse image `u⁻¹ ℱ` the sections of the left Kan extension
over `V` are the filtered colimit of the `ℱ(W)` over the morphisms `V ⟶ u W`; the first half of the
criterion is the joint surjectivity of the colimit maps together with filteredness, the second the
description of equality in a filtered colimit, and sheafification is locally bijective.

## References

* [Stacks Project, Tag 099T](https://stacks.math.columbia.edu/tag/099T)
* [Stacks Project, Tag 099Y](https://stacks.math.columbia.edu/tag/099Y)
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Presheaf

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (u : C ⥤ D)
  (K : GrothendieckTopology D)

/-- **Sections locally coming from the image of `u`.** A presheaf of sets `P` on `D` has this
property if

* every section `s` of `P` over `V`, together with a morphism `k₀ : V ⟶ u W₀`, is locally on `V`
  the restriction of a section over some `u W`, along a morphism `V' ⟶ u W` lying over `k₀` by
  a morphism `W ⟶ W₀` of `C`;
* two sections of `P` over `u W` which agree after restriction to some `V ⟶ u W` agree, locally on
  `V`, after restriction to some `u W' ⟶ u W` through which the restriction factors, for a
  morphism `W' ⟶ W` of `C`. -/
structure IsLocallyFromImage (P : Dᵒᵖ ⥤ Type w) : Prop where
  exists_restriction ⦃V : D⦄ (s : P.obj (op V)) ⦃W₀ : C⦄ (k₀ : V ⟶ u.obj W₀) :
    ∃ S ∈ K V, ∀ ⦃V' : D⦄ ⦃h : V' ⟶ V⦄, S h → ∃ (W : C) (p : W ⟶ W₀) (k : V' ⟶ u.obj W)
      (a : P.obj (op (u.obj W))), k ≫ u.map p = h ≫ k₀ ∧ P.map h.op s = P.map k.op a
  exists_eq ⦃W : C⦄ (a b : P.obj (op (u.obj W))) ⦃V : D⦄ (g : V ⟶ u.obj W)
    (hab : P.map g.op a = P.map g.op b) :
    ∃ S ∈ K V, ∀ ⦃V' : D⦄ ⦃h : V' ⟶ V⦄, S h → ∃ (W' : C) (p : W' ⟶ W) (k : V' ⟶ u.obj W'),
      k ≫ u.map p = h ≫ g ∧ P.map (u.map p).op a = P.map (u.map p).op b

variable {u K}

/-- An isomorphism of sheaves of sets is bijective on sections. -/
private theorem bijective_hom_app_of_isIso {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} {A B : Sheaf J (Type w)} (f : A ⟶ B) [IsIso f] (X : Cᵒᵖ) :
    Function.Bijective (f.hom.app X) :=
  (isIso_iff_bijective _).1 (inferInstanceAs (IsIso (((sheafToPresheaf J (Type w)).map f).app X)))

/-- The criterion is invariant under isomorphism of presheaves. -/
theorem IsLocallyFromImage.of_iso {P Q : Dᵒᵖ ⥤ Type w} (e : P ≅ Q)
    (hP : IsLocallyFromImage u K P) : IsLocallyFromImage u K Q where
  exists_restriction V s W₀ k₀ := by
    obtain ⟨S, hS, hs⟩ := hP.exists_restriction (e.inv.app _ s) k₀
    refine ⟨S, hS, fun V' h hh => ?_⟩
    obtain ⟨W, p, k, a, hk, ha⟩ := hs hh
    refine ⟨W, p, k, e.hom.app _ a, hk, ?_⟩
    calc Q.map h.op s = Q.map h.op (e.hom.app _ (e.inv.app _ s)) := by simp
      _ = e.hom.app _ (P.map h.op (e.inv.app _ s)) := (NatTrans.naturality_apply e.hom _ _).symm
      _ = e.hom.app _ (P.map k.op a) := by rw [ha]
      _ = Q.map k.op (e.hom.app _ a) := NatTrans.naturality_apply e.hom _ _
  exists_eq W a b V g hab := by
    have hab' : P.map g.op (e.inv.app _ a) = P.map g.op (e.inv.app _ b) := by
      rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, hab]
    obtain ⟨S, hS, hs⟩ := hP.exists_eq _ _ g hab'
    refine ⟨S, hS, fun V' h hh => ?_⟩
    obtain ⟨W', p, k, hk, hp⟩ := hs hh
    refine ⟨W', p, k, hk, ?_⟩
    have := congrArg (e.hom.app _) hp
    simpa using this

/-! ### The criterion makes the counit an isomorphism -/

section Counit

variable {J : GrothendieckTopology C} [u.IsContinuous J K]
  {L : Sheaf J (Type w) ⥤ Sheaf K (Type w)} (adj : L ⊣ u.sheafPushforwardContinuous (Type w) J K)

/-- If the unit is invertible, the counit is bijective on sections over the objects `u W`. -/
theorem bijective_counit_app_app [IsIso adj.unit] (Q : Sheaf K (Type w)) (W : C) :
    Function.Bijective ((adj.counit.app Q).hom.app (op (u.obj W))) := by
  have h : IsIso ((u.sheafPushforwardContinuous (Type w) J K).map (adj.counit.app Q)) := by
    rw [IsIso.eq_inv_of_hom_inv_id (adj.right_triangle_components Q)]
    infer_instance
  exact bijective_hom_app_of_isIso ((u.sheafPushforwardContinuous (Type w) J K).map
    (adj.counit.app Q)) (op W)

/-- **The criterion makes the counit an isomorphism.** Let `L ⊣ u_*` with invertible unit, and
suppose `u` carries some object to a final object of `D`. If a sheaf of sets `𝒬` on `D` satisfies
`CategoryTheory.Presheaf.IsLocallyFromImage`, and so does `L u_* 𝒬`, then the counit
`L u_* 𝒬 ⟶ 𝒬` is an isomorphism. -/
theorem isIso_counit_of_isLocallyFromImage [IsIso adj.unit] {T : C} (hT : IsTerminal (u.obj T))
    (Q : Sheaf K (Type w)) (hQ : IsLocallyFromImage u K Q.obj)
    (hP : IsLocallyFromImage u K (L.obj ((u.sheafPushforwardContinuous (Type w) J K).obj Q)).obj) :
    IsIso (adj.counit.app Q) := by
  set P := L.obj ((u.sheafPushforwardContinuous (Type w) J K).obj Q)
  set c := adj.counit.app Q
  have hc : ∀ {V V' : D} (f : V' ⟶ V) (x : P.obj.obj (op V)),
      c.hom.app (op V') (P.obj.map f.op x) = Q.obj.map f.op (c.hom.app (op V) x) :=
    fun f x => NatTrans.naturality_apply c.hom f.op x
  have hbij := bijective_counit_app_app adj Q
  refine (Sheaf.isLocallyBijective_iff_isIso c).1 ⟨⟨fun {V} x y hxy => ?_⟩, ⟨fun {V} s => ?_⟩⟩
  · -- local injectivity
    obtain ⟨S₁, hS₁, hs₁⟩ := hP.exists_restriction x (hT.from V.unop)
    refine K.transitive hS₁ _ fun V₁ h₁ hh₁ => ?_
    obtain ⟨W₁, -, k₁, x₁, -, hx₁⟩ := hs₁ hh₁
    obtain ⟨S₂, hS₂, hs₂⟩ := hP.exists_restriction (P.obj.map h₁.op y) k₁
    refine K.transitive hS₂ _ fun V₂ h₂ hh₂ => ?_
    obtain ⟨W₂, p₂, k₂, y₂, hk₂, hy₂⟩ := hs₂ hh₂
    set x₂ := P.obj.map (u.map p₂).op x₁
    have hx₂ : P.obj.map (h₂ ≫ h₁).op x = P.obj.map k₂.op x₂ := by
      rw [op_comp, FunctorToTypes.map_comp_apply, hx₁, ← FunctorToTypes.map_comp_apply,
        ← op_comp, ← hk₂, op_comp, FunctorToTypes.map_comp_apply]
    have hy₂' : P.obj.map (h₂ ≫ h₁).op y = P.obj.map k₂.op y₂ := by
      rw [op_comp, FunctorToTypes.map_comp_apply, hy₂]
    have hxy₂ : Q.obj.map k₂.op (c.hom.app _ x₂) = Q.obj.map k₂.op (c.hom.app _ y₂) := by
      rw [← hc, ← hc, ← hx₂, ← hy₂', hc, hc]
      exact congrArg _ hxy
    obtain ⟨S₃, hS₃, hs₃⟩ := hQ.exists_eq _ _ k₂ hxy₂
    refine K.superset_covering (fun V₃ h₃ hh₃ => ?_) hS₃
    obtain ⟨W₃, p₃, k₃, hk₃, hp₃⟩ := hs₃ hh₃
    have hp₃' : P.obj.map (u.map p₃).op x₂ = P.obj.map (u.map p₃).op y₂ :=
      (hbij W₃).1 ((hc _ x₂).trans (hp₃.trans (hc _ y₂).symm))
    have e₁ : ∀ z z₂, P.obj.map (h₂ ≫ h₁).op z = P.obj.map k₂.op z₂ →
        P.obj.map ((h₃ ≫ h₂) ≫ h₁).op z = P.obj.map k₃.op (P.obj.map (u.map p₃).op z₂) := by
      intro z z₂ hz
      rw [Category.assoc, op_comp, FunctorToTypes.map_comp_apply, hz,
        ← FunctorToTypes.map_comp_apply, ← op_comp, ← hk₃, op_comp, FunctorToTypes.map_comp_apply]
    exact (e₁ x x₂ hx₂).trans ((congrArg (P.obj.map k₃.op) hp₃').trans (e₁ y y₂ hy₂').symm)
  · -- local surjectivity
    obtain ⟨S, hS, hs⟩ := hQ.exists_restriction s (hT.from V)
    refine K.superset_covering (fun V' h hh => ?_) hS
    obtain ⟨W, -, k, a, -, ha⟩ := hs hh
    obtain ⟨t, rfl⟩ := (hbij W).2 a
    exact ⟨P.obj.map k.op t, (hc k t).trans ha.symm⟩

end Counit

/-! ### Inverse images satisfy the criterion -/

section SheafPullback

variable (J : GrothendieckTopology C) [u.IsContinuous J K] [HasWeakSheafify K (Type w)]
  [K.WEqualsLocallyBijective (Type w)]
  [∀ P : Cᵒᵖ ⥤ Type w, u.op.HasPointwiseLeftKanExtension P]

omit [K.WEqualsLocallyBijective (Type w)] in
/-- The unit of the inverse image constructed as a sheafified left Kan extension is the unit of
the left Kan extension followed by the sheafification map. -/
theorem sheafAdjunctionContinuous_unit_app_hom_app (B : Sheaf J (Type w)) (W : Cᵒᵖ) :
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u (Type w) J K).unit.app
      B).hom.app W =
      (u.op.lanUnit.app B.obj).app W ≫ (toSheafify K (u.op.lan.obj B.obj)).app (u.op.obj W) := by
  show ((sheafToPresheaf J (Type w)).map
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u (Type w) J K).unit.app B)).app
      W = _
  have h := Adjunction.map_restrictFullyFaithful_unit_app
    (L := Functor.sheafPullbackConstruction.sheafPullback u (Type w) J K)
    (R := u.sheafPushforwardContinuous (Type w) J K)
    ((u.op.lanAdjunction (Type w)).comp (sheafificationAdjunction K (Type w)))
    (fullyFaithfulSheafToPresheaf J (Type w)) (Functor.FullyFaithful.id _) (Iso.refl _)
    (Iso.refl _) B
  refine (congrArg (fun f => NatTrans.app f W) h).trans ?_
  simp [Adjunction.comp_unit_app, Functor.lanAdjunction_unit]
  rfl

omit [K.WEqualsLocallyBijective (Type w)] in
/-- `CategoryTheory.Presheaf.sheafAdjunctionContinuous_unit_app_hom_app` on sections. -/
theorem sheafAdjunctionContinuous_unit_app_hom_app_apply (B : Sheaf J (Type w)) (W : C)
    (y : B.obj.obj (op W)) :
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u (Type w) J K).unit.app
      B).hom.app (op W) y =
      (toSheafify K (u.op.lan.obj B.obj)).app (op (u.obj W))
        ((u.op.lanUnit.app B.obj).app (op W) y) := by
  rw [sheafAdjunctionContinuous_unit_app_hom_app]
  rfl

/-- A section of the left Kan extension of `B` along `u.op` over `V` is the restriction, along
some `V ⟶ u W`, of the image of a section of `B` over `W` under the unit. -/
theorem exists_lan_map_lanUnit (B : Cᵒᵖ ⥤ Type w) {V : D} (x : (u.op.lan.obj B).obj (op V)) :
    ∃ (W : C) (k : V ⟶ u.obj W) (y : B.obj (op W)),
      (u.op.lan.obj B).map k.op ((u.op.lanUnit.app B).app (op W) y) = x := by
  obtain ⟨g, y, hy⟩ := Types.jointly_surjective_of_isColimit
    (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit u.op B (op V)) x
  exact ⟨g.left.unop, g.hom.unop, y, hy⟩

variable {J} in
/-- **Inverse images satisfy the criterion.** If `u` is representably flat and the unit of the
inverse image is invertible at `B`, then the inverse image `u⁻¹ B`, computed as the sheafified
left Kan extension, satisfies `CategoryTheory.Presheaf.IsLocallyFromImage`. -/
theorem isLocallyFromImage_sheafPullback [RepresentablyFlat u] (B : Sheaf J (Type w))
    [IsIso ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u (Type w) J K).unit.app
      B)] :
    IsLocallyFromImage u K
      ((Functor.sheafPullbackConstruction.sheafPullback u (Type w) J K).obj B).obj := by
  have hfilt : ∀ V : D, IsFiltered (CostructuredArrow u.op (op V)) := fun V =>
    IsFiltered.of_equivalence (structuredArrowOpEquivalence u V)
  set F := u.op.lan.obj B.obj
  set α := u.op.lanUnit.app B.obj
  have hP : ((Functor.sheafPullbackConstruction.sheafPullback u (Type w) J K).obj B).obj =
      sheafify K F := rfl
  rw [hP]
  -- naturality of the unit of the left Kan extension, in the form used below
  have hα : ∀ {W W' : C} (p : W' ⟶ W) (y : B.obj.obj (op W)),
      F.map (u.map p).op (α.app (op W) y) = α.app (op W') (B.obj.map p.op y) :=
    fun p y => (NatTrans.naturality_apply α p.op y).symm
  have hσ : ∀ {V V' : D} (f : V' ⟶ V) (x : F.obj (op V)),
      (toSheafify K F).app (op V') (F.map f.op x) =
        (sheafify K F).map f.op ((toSheafify K F).app (op V) x) :=
    fun f x => NatTrans.naturality_apply (toSheafify K F) f.op x
  constructor
  · intro V s W₀ k₀
    refine ⟨_, Presheaf.imageSieve_mem K (toSheafify K F) s, fun V' h ⟨x, hx⟩ => ?_⟩
    obtain ⟨W₁, k₁, y, rfl⟩ := exists_lan_map_lanUnit B.obj x
    let g₁ : CostructuredArrow u.op (op V') := CostructuredArrow.mk k₁.op
    let g₀ : CostructuredArrow u.op (op V') := CostructuredArrow.mk (h ≫ k₀).op
    let g := IsFiltered.max g₁ g₀
    let φ₁ := IsFiltered.leftToMax g₁ g₀
    let φ₀ := IsFiltered.rightToMax g₁ g₀
    have hφ₁ : g.hom.unop ≫ u.map φ₁.left.unop = k₁ :=
      congrArg Quiver.Hom.unop (CostructuredArrow.w φ₁)
    have hφ₀ : g.hom.unop ≫ u.map φ₀.left.unop = h ≫ k₀ :=
      congrArg Quiver.Hom.unop (CostructuredArrow.w φ₀)
    refine ⟨g.left.unop, φ₀.left.unop, g.hom.unop,
      (toSheafify K F).app _ (α.app g.left (B.obj.map φ₁.left y)), hφ₀, ?_⟩
    rw [← hx, ← hσ, ← hφ₁, op_comp, F.map_comp, types_comp_apply]
    show _ = (toSheafify K F).app _ (F.map g.hom (α.app g.left (B.obj.map φ₁.left y)))
    congr 2
    exact hα φ₁.left.unop y
  · intro W a b V g hab
    set η := (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u (Type w) J K).unit.app
      B
    have hηbij := bijective_hom_app_of_isIso η (op W)
    have hη : ∀ (W : C) (y : B.obj.obj (op W)),
        η.hom.app (op W) y = (toSheafify K F).app (op (u.obj W)) (α.app (op W) y) := fun W y =>
      sheafAdjunctionContinuous_unit_app_hom_app_apply J B W y
    obtain ⟨a', rfl⟩ := hηbij.2 a
    obtain ⟨b', rfl⟩ := hηbij.2 b
    rw [hη, hη, ← hσ, ← hσ] at hab
    refine ⟨_, Presheaf.equalizerSieve_mem K (toSheafify K F) _ _ hab, fun V' h hh => ?_⟩
    change F.map h.op (F.map g.op (α.app (op W) a')) =
      F.map h.op (F.map g.op (α.app (op W) b')) at hh
    rw [← types_comp_apply (F.map g.op), ← F.map_comp, ← types_comp_apply (F.map g.op) (F.map h.op),
      ← F.map_comp, ← op_comp] at hh
    obtain ⟨g', φ, hφ⟩ := (Types.FilteredColimit.isColimit_eq_iff'
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit u.op B.obj (op V'))
      (i := CostructuredArrow.mk (h ≫ g).op) a' b').1 hh
    have hφw : g'.hom.unop ≫ u.map φ.left.unop = h ≫ g :=
      congrArg Quiver.Hom.unop (CostructuredArrow.w φ)
    refine ⟨g'.left.unop, φ.left.unop, g'.hom.unop, hφw, ?_⟩
    rw [hη, hη, ← hσ, ← hσ, hα, hα]
    exact congrArg _ (congrArg (α.app g'.left) hφ)

end SheafPullback

/-! ### The criterion is local -/

section Local

variable {J : GrothendieckTopology C}

/-- A property of morphisms into `V` which is stable under precomposition and holds, locally, on
the members of a covering sieve, holds on a covering sieve. -/
lemma exists_covering_of_forall_exists_covering {V : D}
    (Φ : ∀ ⦃V' : D⦄, (V' ⟶ V) → Prop)
    (hΦ : ∀ ⦃V' V'' : D⦄ (h : V' ⟶ V) (g : V'' ⟶ V'), Φ h → Φ (g ≫ h))
    {S : Sieve V} (hS : S ∈ K V)
    (h : ∀ ⦃V' : D⦄ ⦃h : V' ⟶ V⦄, S h → ∃ R ∈ K V', ∀ ⦃V'' : D⦄ ⦃g : V'' ⟶ V'⦄, R g →
      Φ (g ≫ h)) :
    ∃ T ∈ K V, ∀ ⦃V' : D⦄ ⦃h : V' ⟶ V⦄, T h → Φ h :=
  ⟨⟨fun _ h => Φ h, fun hh g => hΦ _ g hh⟩, K.transitive hS _ fun _ _ hh => by
    obtain ⟨R, hR, hr⟩ := h hh
    exact K.superset_covering (fun _ g hg => hr hg) hR, fun _ _ hh => hh⟩

/-- **The criterion is local on `C`.** Let `u` be cover preserving. If every object `W₀` of `C`
has a covering by objects `W` over which `P` is isomorphic to a presheaf satisfying the
criterion — isomorphic on the slice `D/u W`, i.e. on the sections over the objects of `D` over
`u W`, compatibly with restriction over `u W` — then `P` satisfies the criterion. -/
theorem IsLocallyFromImage.of_locallyIso (hu : CoverPreserving J K u) (P : Dᵒᵖ ⥤ Type w)
    (hloc : ∀ W₀ : C, ∃ S ∈ J W₀, ∀ ⦃W : C⦄ ⦃f : W ⟶ W₀⦄, S f →
      ∃ P' : Dᵒᵖ ⥤ Type w, IsLocallyFromImage u K P' ∧
        Nonempty ((Over.forget (u.obj W)).op ⋙ P ≅ (Over.forget (u.obj W)).op ⋙ P')) :
    IsLocallyFromImage u K P := by
  have hih : ∀ {W : C} {P' : Dᵒᵖ ⥤ Type w}
      (e : (Over.forget (u.obj W)).op ⋙ P ≅ (Over.forget (u.obj W)).op ⋙ P')
      (X : Over (u.obj W)) (y : P.obj (op X.left)), e.inv.app (op X) (e.hom.app (op X) y) = y :=
    by intro W P' e X y; simp
  constructor
  · intro V s W₀ k₀
    obtain ⟨S, hS, hSloc⟩ := hloc W₀
    refine exists_covering_of_forall_exists_covering _ (fun _ _ h g ⟨W, p, k, a, hk, ha⟩ =>
      ⟨W, p, g ≫ k, a, by rw [Category.assoc, hk, Category.assoc], by
        rw [op_comp, FunctorToTypes.map_comp_apply, ha, ← FunctorToTypes.map_comp_apply,
          op_comp]⟩) (K.pullback_stable k₀ (hu.cover_preserve hS)) fun V₁ h₁ hh₁ => ?_
    obtain ⟨W₁, f₁, k₁, hf₁, hk₁⟩ := hh₁
    obtain ⟨P', hP', ⟨e⟩⟩ := hSloc hf₁
    obtain ⟨R, hR, hr⟩ := hP'.exists_restriction
      (e.hom.app (op (Over.mk k₁)) (P.map h₁.op s)) k₁
    refine ⟨R, hR, fun V₂ g hg => ?_⟩
    obtain ⟨W, p, k, a, hk, ha⟩ := hr hg
    refine ⟨W, p ≫ f₁, k, e.inv.app (op (Over.mk (u.map p))) a, ?_, ?_⟩
    · rw [u.map_comp, ← Category.assoc, hk, Category.assoc, ← hk₁, Category.assoc]
    · have e₁ : e.hom.app (op (Over.mk (g ≫ k₁))) (P.map (g ≫ h₁).op s) = P'.map k.op a := by
        rw [op_comp, FunctorToTypes.map_comp_apply]
        exact (NatTrans.naturality_apply e.hom
          (Over.homMk g : Over.mk (g ≫ k₁) ⟶ Over.mk k₁).op _).trans ha
      have e₂ : e.inv.app (op (Over.mk (g ≫ k₁))) (P'.map k.op a) =
          P.map k.op (e.inv.app (op (Over.mk (u.map p))) a) :=
        NatTrans.naturality_apply e.inv
          (Over.homMk k (by simpa using hk) : Over.mk (g ≫ k₁) ⟶ Over.mk (u.map p)).op a
      rw [← e₁, hih] at e₂
      exact e₂
  · intro W a b V g hab
    obtain ⟨S, hS, hSloc⟩ := hloc W
    refine exists_covering_of_forall_exists_covering _ (fun _ _ h g' ⟨W', p, k, hk, hp⟩ =>
      ⟨W', p, g' ≫ k, by rw [Category.assoc, hk, Category.assoc], hp⟩)
      (K.pullback_stable g (hu.cover_preserve hS)) fun V₁ h₁ hh₁ => ?_
    obtain ⟨W₁, f₁, k₁, hf₁, hk₁⟩ := hh₁
    obtain ⟨P', hP', ⟨e⟩⟩ := hSloc hf₁
    have hres : ∀ c : P.obj (op (u.obj W)), P'.map k₁.op
        (e.hom.app (op (Over.mk (𝟙 _))) (P.map (u.map f₁).op c)) =
          e.hom.app (op (Over.mk k₁)) (P.map (h₁ ≫ g).op c) := by
      intro c
      refine (NatTrans.naturality_apply e.hom
        (Over.homMk k₁ (by simp) : Over.mk k₁ ⟶ Over.mk (𝟙 (u.obj W₁))).op _).symm.trans
        (congrArg (e.hom.app _) ?_)
      show P.map k₁.op (P.map (u.map f₁).op c) = _
      rw [← FunctorToTypes.map_comp_apply, ← op_comp, hk₁]
    have hab₁ : P'.map k₁.op (e.hom.app (op (Over.mk (𝟙 _))) (P.map (u.map f₁).op a)) =
        P'.map k₁.op (e.hom.app (op (Over.mk (𝟙 _))) (P.map (u.map f₁).op b)) := by
      rw [hres, hres, op_comp, FunctorToTypes.map_comp_apply, FunctorToTypes.map_comp_apply, hab]
    obtain ⟨R, hR, hr⟩ := hP'.exists_eq _ _ k₁ hab₁
    refine ⟨R, hR, fun V₂ g₂ hg₂ => ?_⟩
    obtain ⟨W₂, p, k₂, hk₂, hp⟩ := hr hg₂
    refine ⟨W₂, p ≫ f₁, k₂, ?_, ?_⟩
    · rw [u.map_comp, ← Category.assoc, hk₂, Category.assoc, ← hk₁, Category.assoc]
    · have hc : ∀ c : P.obj (op (u.obj W)), P.map (u.map (p ≫ f₁)).op c =
          e.inv.app (op (Over.mk (u.map p))) (P'.map (u.map p).op
            (e.hom.app (op (Over.mk (𝟙 _))) (P.map (u.map f₁).op c))) := by
        intro c
        refine Eq.trans ?_ (NatTrans.naturality_apply e.inv (Over.homMk (u.map p) (by simp) :
          Over.mk (u.map p) ⟶ Over.mk (𝟙 (u.obj W₁))).op _).symm
        rw [hih]
        show _ = P.map (u.map p).op (P.map (u.map f₁).op c)
        rw [← FunctorToTypes.map_comp_apply, ← op_comp, u.map_comp]
      rw [hc, hc]
      exact congrArg _ hp

end Local


end CategoryTheory.Presheaf

end
