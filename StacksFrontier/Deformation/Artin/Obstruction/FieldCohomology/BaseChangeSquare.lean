module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.IntoField
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveTheory

/-!
# The field base-change map and the (RS*) base-change square

Linear duality over a field, the map `E_x ⊗^L_A k ⟶ E_y ⊗^L_B k` of a naive obstruction theory
at a field-valued point, lifts across categorical pullback and (RS*) squares, and the square
`A[M] = A ×_{A'} A'[N]` and its incarnation in the site.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace Deformation.Artin

attribute [local instance] HasDerivedCategory.standard

/-! ### Linear duality over a field -/

/-- If two maps are intertwined by a pair of equivalences, one is bijective iff the other is. -/
private theorem bijective_of_equiv_comm {α β γ δ : Type*} (e₁ : α ≃ γ) (e₂ : β ≃ δ)
    (f : α → β) (g : γ → δ) (h : ∀ a, g (e₁ a) = e₂ (f a)) (hf : Function.Bijective f) :
    Function.Bijective g := by
  have : g = e₂ ∘ f ∘ e₁.symm := funext fun c => by simpa using h (e₁.symm c)
  rw [this]
  exact e₂.bijective.comp (hf.comp e₁.symm.bijective)

/-- A `k`-linear map is bijective as soon as precomposition with it is a bijection on the
functionals with values in the rank-one space. -/
public theorem bijective_of_bijective_dualPrecomp {k : Type u} [Field k]
    {V W : ModuleCat.{u} k} (φ : V ⟶ W)
    (hφ : Function.Bijective
      (fun ψ : W ⟶ ModuleCat.of k (ULift.{u} k) => φ ≫ ψ)) :
    Function.Bijective φ.hom := by
  let uk : ULift.{u} k ≃ₗ[k] k := ULift.moduleEquiv
  let e : ∀ X : ModuleCat.{u} k, (X ⟶ ModuleCat.of k (ULift.{u} k)) ≃ (X →ₗ[k] k) :=
    fun X =>
      { toFun := fun ψ => uk.toLinearMap ∘ₗ ψ.hom
        invFun := fun l => ModuleCat.ofHom (uk.symm.toLinearMap ∘ₗ l)
        left_inv := fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => uk.symm_apply_apply _)
        right_inv := fun _ => LinearMap.ext fun _ => uk.apply_symm_apply _ }
  refine LinearMap.dualMap_bijective_iff.mp ?_
  exact bijective_of_equiv_comm (e W) (e V) _ _ (fun _ => LinearMap.ext fun _ => rfl) hφ

/-! ### Comparison of the two pullbacks of `Ext` classes over a change of rings -/

/-- Pushing an `Ext` class forward along an isomorphism of coefficient modules is a
bijection. -/
public theorem bijective_extPushforward_of_isIso {A : Type u} [CommRing A]
    (E : DerivedCategory (ModuleCat.{u} A)) {M N : ModuleCat.{u} A} (m : M ⟶ N) [IsIso m]
    (i : ℤ) : Function.Bijective (extPushforward E m i) := by
  let q := ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map m)⟦i⟧'
  have hq : IsIso q := inferInstance
  constructor
  · exact fun α β hαβ => (cancel_mono q).mp (hαβ : α ≫ q = β ≫ q)
  · intro β
    refine ⟨β ≫ CategoryTheory.inv q, ?_⟩
    show (β ≫ CategoryTheory.inv q) ≫ q = β
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- The pullback of an `Ext` class into a field across a change of source ring is the pullback
of that class over the change of rings, pushed forward along the canonical comparison of the
two restrictions of the field to the source ring. -/
public theorem extIntoFieldRestriction_eq_extPushforward
    {A A' k : Type u} [CommRing A] [CommRing A'] [Field k]
    (f : A →+* A') (g : A' →+* k)
    (E : DerivedCategory (ModuleCat.{u} A)) (F : DerivedCategory (ModuleCat.{u} A'))
    (c : E ⟶ (ModuleCat.restrictScalars f).mapDerivedCategory.obj F) (i : ℤ)
    (α : DerivedCategory.Ext F ((DerivedCategory.singleFunctor (ModuleCat.{u} A') 0).obj
      ((ModuleCat.restrictScalars g).obj (ModuleCat.of k (ULift.{u} k)))) i) :
    DerivedCategory.extIntoFieldRestriction.{u, u, u, u} f g E F c i α =
      extPushforward E
        ((ModuleCat.restrictScalarsComp f g).app (ModuleCat.of k (ULift.{u} k))).inv i
        (extRestrictScalars f E F c
          ((ModuleCat.restrictScalars g).obj (ModuleCat.of k (ULift.{u} k))) i α) := by
  simp only [DerivedCategory.extIntoFieldRestriction, extPushforward, extRestrictScalars,
    Functor.mapDerivedCategorySingleFunctor, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]

/-! ### Cohomology of derived base change along a change of source ring -/

/-- If pulling `Ext` classes into a field back along a morphism `E ⟶ Res_f F` over a ring map
`f : A → A'` is bijective in degree `i`, then the induced map
`H^{-i}(E ⊗^L_A k) ⟶ H^{-i}(F ⊗^L_{A'} k)` is bijective. -/
public theorem bijective_homologyFunctor_map_derivedBaseChangeMap
    {A A' k : Type u} [CommRing A] [CommRing A'] [Field k]
    (f : A →+* A') (g : A' →+* k)
    (E : DerivedCategory.Minus (ModuleCat.{u} A))
    (F : DerivedCategory.Minus (ModuleCat.{u} A'))
    (c : E.obj ⟶ (ModuleCat.restrictScalars f).mapDerivedCategory.obj F.obj) (i : ℤ)
    (hbij : Function.Bijective
      (DerivedCategory.extIntoFieldRestriction.{u, u, u, u} f g E.obj F.obj c i)) :
    Function.Bijective ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) (-i)).map
      (DerivedCategory.derivedBaseChangeMap.{u, u, u, u} f g E.obj F.obj c)).hom := by
  refine bijective_of_bijective_dualPrecomp _ ?_
  have hclause := DerivedCategory.extIntoFieldEquivDualBaseChangeHomology_restrictScalars.{u,
    u, u, u} f g E F c i
  exact bijective_of_equiv_comm
    (DerivedCategory.extIntoFieldEquivDualBaseChangeHomology.{u, u, u} g F i).toEquiv
    (DerivedCategory.extIntoFieldEquivDualBaseChangeHomology.{u, u, u} (g.comp f) E i).toEquiv
    _ _ (fun α => (hclause α).symm) hbij

/-! ### The functoriality map of a naive obstruction theory at a field-valued point -/

/-- In a commuting square `push ∘ u = r ∘ u' ∘ τ`, `r` is bijective when `u` and `push` are
bijective and `τ` and `u'` are surjective. -/
private theorem bijective_of_comm_square {T₁ T₂ E₁ E₂ E₃ : Type*} (u : T₁ → E₁)
    (push : E₁ → E₂) (τ : T₁ → T₂) (u' : T₂ → E₃) (r : E₃ → E₂)
    (hcomm : ∀ a, push (u a) = r (u' (τ a))) (hu : Function.Bijective u)
    (hpush : Function.Bijective push) (hτ : Function.Surjective τ)
    (hu' : Function.Surjective u') : Function.Bijective r := by
  have hvu : Function.Bijective (r ∘ (u' ∘ τ)) :=
    (funext hcomm : push ∘ u = r ∘ (u' ∘ τ)) ▸ hpush.comp hu
  refine ⟨fun b b' hbb' => ?_, fun z => ?_⟩
  · obtain ⟨a, rfl⟩ := (hu'.comp hτ) b
    obtain ⟨a', rfl⟩ := (hu'.comp hτ) b'
    exact congrArg (u' ∘ τ) (hvu.1 hbb')
  · obtain ⟨a, ha⟩ := hvu.2 z
    exact ⟨(u' ∘ τ) a, ha⟩

/-- The field `k`, viewed as a module over a ring mapping to it, as a module of the chosen
big site. -/
public abbrev fieldSiteModule (R : Type u) [CommRing R] (Bs : BigFppfSite.{u}) {k : Type u}
    [Field k] (g : R →+* k)
    (hg : IsSiteModule R Bs
      ((ModuleCat.restrictScalars g).obj (ModuleCat.of k (ULift.{u} k)))) :
    SiteModule R Bs :=
  ⟨_, hg⟩

/-- The canonical comparison of the two module structures that a ring map `A ⟶ A'` puts on a
field receiving `A'`: the semilinear map over `A ⟶ A'` relating the site modules of the
field. -/
public abbrev fieldSiteModuleComparison {A A' : Type u} [CommRing A] [CommRing A']
    (f : A →+* A') (Bs : BigFppfSite.{u}) {k : Type u} [Field k] (g : A' →+* k)
    (hM : IsSiteModule A Bs ((ModuleCat.restrictScalars (g.comp f)).obj
      (ModuleCat.of k (ULift.{u} k))))
    (hN : IsSiteModule A' Bs ((ModuleCat.restrictScalars g).obj
      (ModuleCat.of k (ULift.{u} k)))) :
    (fieldSiteModule A Bs (g.comp f) hM).obj ⟶
      (ModuleCat.restrictScalars f).obj (fieldSiteModule A' Bs g hN).obj :=
  ((ModuleCat.restrictScalarsComp f g).app (ModuleCat.of k (ULift.{u} k))).hom

section Fibre

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS}
  {hp : p.IsFiberedInGroupoids} {hRS : SatisfiesRSStar B S hS p hp} {c : AffineChart S}

/-- The transformation `T_x(M) → Ext^0_A(E_x, M)` of a naive obstruction theory turns
bijectivity of the transition on lift classes into bijectivity of the pullback of `Ext^0`
classes along the functoriality map `E_x → E_y`. -/
public theorem bijective_extRestrictScalars_zero_of_bijective_tangentTransition
    (nob : NaiveObstructionTheory B S hS p hp hRS c)
    (P Q : ChartedObject B S hS p c) (h : AffineObject.Hom P.obj Q.obj)
    [Algebra P.ring Q.ring] [IsScalarTower c.ring P.ring Q.ring]
    (halg : algebraMap P.ring Q.ring = h.alg.ringMap)
    (M : SiteModule P.ring B) (N : SiteModule Q.ring B)
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars (algebraMap P.ring Q.ring)).obj N.obj) [IsIso ψ]
    (htan : ∀ τ : ((P.tangent hp hRS).functor.obj M : Type (max (u + 1) v w)) →
        ((Q.tangent hp hRS).functor.obj N : Type (max (u + 1) v w)),
      (∀ a, IsSquareZeroLiftBaseChange h (algebraMap P.ring Q.ring) ψ
        ((P.tangent hp hRS).liftEquiv M a) ((Q.tangent hp hRS).liftEquiv N (τ a))) →
      Function.Bijective τ) :
    Function.Bijective (extRestrictScalars (algebraMap P.ring Q.ring) (nob.complex P).obj
      (nob.complex Q).obj (nob.functoriality P Q h halg) N.obj 0) := by
  obtain ⟨τ, hτ₁, hτ₂⟩ := nob.tangentMap_functoriality P Q h halg M N ψ
  exact bijective_of_comm_square _ _ τ _ _ hτ₂ (nob.tangentMap_bijective P M)
    (bijective_extPushforward_of_isIso _ ψ 0) (htan τ hτ₁).2 (nob.tangentMap_bijective Q N).2

/-- The transformation `Inf_x(M) → Ext^{-1}_A(E_x, M)` of a naive obstruction theory turns
bijectivity of the transition on infinitesimal automorphisms into bijectivity of the pullback
of `Ext^{-1}` classes along the functoriality map `E_x → E_y`. -/
public theorem bijective_extRestrictScalars_negOne_of_bijective_infTransition
    (nob : NaiveObstructionTheory B S hS p hp hRS c)
    (P Q : ChartedObject B S hS p c) (h : AffineObject.Hom P.obj Q.obj)
    [Algebra P.ring Q.ring] [IsScalarTower c.ring P.ring Q.ring]
    (halg : algebraMap P.ring Q.ring = h.alg.ringMap)
    (M : SiteModule P.ring B) (N : SiteModule Q.ring B)
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars (algebraMap P.ring Q.ring)).obj N.obj) [IsIso ψ]
    (hinf : ∀ σ : ((P.infAut hp hRS).functor.obj M : Type w) →
        ((Q.infAut hp hRS).functor.obj N : Type w),
      (∀ θ, IsInfinitesimalAutomorphismBaseChange hp h (algebraMap P.ring Q.ring) ψ
        ((P.infAut hp hRS).autEquiv M θ) ((Q.infAut hp hRS).autEquiv N (σ θ))) →
      Function.Bijective σ) :
    Function.Bijective (extRestrictScalars (algebraMap P.ring Q.ring) (nob.complex P).obj
      (nob.complex Q).obj (nob.functoriality P Q h halg) N.obj (-1)) := by
  obtain ⟨σ, hσ₁, hσ₂⟩ := nob.infMap_functoriality P Q h halg M N ψ
  exact bijective_of_comm_square _ _ σ _ _ hσ₂ (nob.infMap_bijective P M)
    (bijective_extPushforward_of_isIso _ ψ (-1)) (hinf σ hσ₁).2 (nob.infMap_bijective Q N).2

/-- The map `E_x ⊗^L_A k ⟶ E_y ⊗^L_B k` of derived base changes to a field `k` receiving `B`,
induced by the functoriality map `E_x ⟶ E_y` of a naive obstruction theory along a ring map
`A ⟶ B` of charted objects. -/
public abbrev naiveObstructionFieldBaseChangeMap
    (nob : NaiveObstructionTheory B S hS p hp hRS c)
    (P Q : ChartedObject B S hS p c) (h : AffineObject.Hom P.obj Q.obj)
    [Algebra P.ring Q.ring] [IsScalarTower c.ring P.ring Q.ring]
    (halg : algebraMap P.ring Q.ring = h.alg.ringMap)
    {k : Type u} [Field k] (g : Q.ring →+* k) :=
  DerivedCategory.derivedBaseChangeMap.{u, u, u, u} (algebraMap P.ring Q.ring) g
    (nob.complex P).obj (nob.complex Q).obj (nob.functoriality P Q h halg)

/-- **Stacks 07YT, modulo the Rim–Schlessinger step.** Let `𝒳` be endowed with a naive
obstruction theory, let `y ⟶ x` lie over a ring map `A ⟶ B` of charted objects and let `k` be
a `B`-algebra which is a field. If the transitions of Stacks 07YA on lift classes and on
infinitesimal automorphisms with coefficients in `k` are bijective, then the functoriality map
`E_x ⟶ E_y` induces bijections `H^i(E_x ⊗^L_A k) ⟶ H^i(E_y ⊗^L_B k)` for `i = 0, 1`. -/
public theorem bijective_homologyFunctor_map_naiveObstructionFieldBaseChangeMap
    (nob : NaiveObstructionTheory B S hS p hp hRS c)
    (P Q : ChartedObject B S hS p c) (h : AffineObject.Hom P.obj Q.obj)
    [Algebra P.ring Q.ring] [IsScalarTower c.ring P.ring Q.ring]
    (halg : algebraMap P.ring Q.ring = h.alg.ringMap)
    {k : Type u} [Field k] (g : Q.ring →+* k)
    (hM : IsSiteModule P.ring B
      ((ModuleCat.restrictScalars (g.comp (algebraMap P.ring Q.ring))).obj
        (ModuleCat.of k (ULift.{u} k))))
    (hN : IsSiteModule Q.ring B
      ((ModuleCat.restrictScalars g).obj (ModuleCat.of k (ULift.{u} k))))
    (htan : ∀ τ : ((P.tangent hp hRS).functor.obj
          (fieldSiteModule P.ring B (g.comp (algebraMap P.ring Q.ring)) hM) :
            Type (max (u + 1) v w)) →
        ((Q.tangent hp hRS).functor.obj (fieldSiteModule Q.ring B g hN) :
          Type (max (u + 1) v w)),
      (∀ a, IsSquareZeroLiftBaseChange h (algebraMap P.ring Q.ring)
        (fieldSiteModuleComparison (algebraMap P.ring Q.ring) B g hM hN)
        ((P.tangent hp hRS).liftEquiv _ a) ((Q.tangent hp hRS).liftEquiv _ (τ a))) →
      Function.Bijective τ)
    (hinf : ∀ σ : ((P.infAut hp hRS).functor.obj
          (fieldSiteModule P.ring B (g.comp (algebraMap P.ring Q.ring)) hM) : Type w) →
        ((Q.infAut hp hRS).functor.obj (fieldSiteModule Q.ring B g hN) : Type w),
      (∀ θ, IsInfinitesimalAutomorphismBaseChange hp h (algebraMap P.ring Q.ring)
        (fieldSiteModuleComparison (algebraMap P.ring Q.ring) B g hM hN)
        ((P.infAut hp hRS).autEquiv _ θ) ((Q.infAut hp hRS).autEquiv _ (σ θ))) →
      Function.Bijective σ) :
    Function.Bijective ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).map
        (naiveObstructionFieldBaseChangeMap nob P Q h halg g)).hom ∧
      Function.Bijective ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 1).map
        (naiveObstructionFieldBaseChangeMap nob P Q h halg g)).hom := by
  have hr₀ := bijective_extRestrictScalars_zero_of_bijective_tangentTransition nob P Q h halg
    (fieldSiteModule P.ring B (g.comp (algebraMap P.ring Q.ring)) hM)
    (fieldSiteModule Q.ring B g hN)
    (fieldSiteModuleComparison (algebraMap P.ring Q.ring) B g hM hN) htan
  have hr₁ := bijective_extRestrictScalars_negOne_of_bijective_infTransition nob P Q h halg
    (fieldSiteModule P.ring B (g.comp (algebraMap P.ring Q.ring)) hM)
    (fieldSiteModule Q.ring B g hN)
    (fieldSiteModuleComparison (algebraMap P.ring Q.ring) B g hM hN) hinf
  have hbridge : ∀ i : ℤ,
      DerivedCategory.extIntoFieldRestriction.{u, u, u, u} (algebraMap P.ring Q.ring) g
          (nob.complex P).obj (nob.complex Q).obj (nob.functoriality P Q h halg) i =
        extPushforward (nob.complex P).obj
            ((ModuleCat.restrictScalarsComp (algebraMap P.ring Q.ring) g).app
              (ModuleCat.of k (ULift.{u} k))).inv i ∘
          extRestrictScalars (algebraMap P.ring Q.ring) (nob.complex P).obj
            (nob.complex Q).obj (nob.functoriality P Q h halg)
            ((ModuleCat.restrictScalars g).obj (ModuleCat.of k (ULift.{u} k))) i :=
    fun i => funext (extIntoFieldRestriction_eq_extPushforward (algebraMap P.ring Q.ring) g
      (nob.complex P).obj (nob.complex Q).obj (nob.functoriality P Q h halg) i)
  have hb : ∀ i : ℤ, Function.Bijective (extRestrictScalars (algebraMap P.ring Q.ring)
      (nob.complex P).obj (nob.complex Q).obj (nob.functoriality P Q h halg)
      ((ModuleCat.restrictScalars g).obj (ModuleCat.of k (ULift.{u} k))) i) →
      Function.Bijective ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) (-i)).map
        (naiveObstructionFieldBaseChangeMap nob P Q h halg g)).hom := fun i hr =>
    bijective_homologyFunctor_map_derivedBaseChangeMap (algebraMap P.ring Q.ring) g
      (nob.complex P) (nob.complex Q) (nob.functoriality P Q h halg) i
      (by rw [hbridge i]; exact (bijective_extPushforward_of_isIso _ _ i).comp hr)
  exact ⟨by simpa using hb 0 hr₀, by simpa using hb (-1) hr₁⟩

end Fibre

/-! ### Lifts of a point of a corner of a categorical pullback square -/

/- The arrow of a lift across the first projection of a categorical pullback has source the
image of the point under that projection, while the structural isomorphism of the point has
its source spelled by the first component instead; naming the projection here is what makes
the goals below type-correct at the `implicit` transparency level. -/
attribute [local implicit_reducible] CategoryTheory.Limits.CategoricalPullback.π₁

section CategoricalPullbackLift

open CategoryTheory.Limits CategoryTheory.Functor

variable {A₁ A₂ A₃ : Type*} [Category A₁] [Category A₂] [Category A₃]
  (F : A₁ ⥤ A₃) (G : A₂ ⥤ A₃) (x : A₁)

/-- The lift of `F x` across `G` carried by a lift of `x` across the first projection of a
categorical pullback: the second component of the point, with its structure arrow read
through the structural isomorphism of the point. -/
@[implicit_reducible] public def categoricalPullbackIsoFiberRestrict :
    IsoFiber (CategoricalPullback.π₁ F G) x ⥤ IsoFiber G (F.obj x) where
  obj t :=
    ⟨CostructuredArrow.mk (S := G) (T := F.obj x)
        (t.obj.left.iso.inv ≫ F.map t.obj.hom),
      have : IsIso t.obj.hom := t.property
      show IsIso (t.obj.left.iso.inv ≫ F.map t.obj.hom) from inferInstance⟩
  map {s t} m :=
    ObjectProperty.homMk (CostructuredArrow.homMk m.hom.left.snd (by
      have hfst : m.hom.left.fst ≫ t.obj.hom = s.obj.hom := CostructuredArrow.w m.hom
      have hw : G.map m.hom.left.snd ≫ t.obj.left.iso.inv =
          s.obj.left.iso.inv ≫ F.map m.hom.left.fst :=
        CategoricalPullback.Hom.w' m.hom.left
      change G.map m.hom.left.snd ≫ t.obj.left.iso.inv ≫ F.map t.obj.hom =
        s.obj.left.iso.inv ≫ F.map s.obj.hom
      rw [← Category.assoc, hw, Category.assoc, ← F.map_comp, hfst]))
  map_id _ := ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ rfl)
  map_comp _ _ := ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ rfl)

/-- The comparison is faithful: a morphism of lifts across the first projection is determined
by its second component, the first being forced by the structure arrows. -/
public theorem categoricalPullbackIsoFiberRestrict_faithful :
    (categoricalPullbackIsoFiberRestrict F G x).Faithful where
  map_injective {s t} m n h := by
    have ht : IsIso t.obj.hom := t.property
    have hm : m.hom.left.fst ≫ t.obj.hom = s.obj.hom := CostructuredArrow.w m.hom
    have hn : n.hom.left.fst ≫ t.obj.hom = s.obj.hom := CostructuredArrow.w n.hom
    have hsnd : m.hom.left.snd = n.hom.left.snd := congrArg (fun z => z.hom.left) h
    apply ObjectProperty.hom_ext
    refine CostructuredArrow.hom_ext _ _ (CategoricalPullback.hom_ext ?_ hsnd)
    exact (cancel_mono t.obj.hom).mp (hm.trans hn.symm)

/-- The comparison is full: a morphism of the carried lifts of `F x` is the second component
of a morphism of lifts of `x`, whose first component is read off from the structure arrows. -/
public theorem categoricalPullbackIsoFiberRestrict_full :
    (categoricalPullbackIsoFiberRestrict F G x).Full where
  map_surjective {s t} ν := by
    have hs : IsIso s.obj.hom := s.property
    have ht : IsIso t.obj.hom := t.property
    have hν : G.map ν.hom.left ≫ t.obj.left.iso.inv ≫ F.map t.obj.hom =
        s.obj.left.iso.inv ≫ F.map s.obj.hom := CostructuredArrow.w ν.hom
    have h₁ : F.map s.obj.hom = s.obj.left.iso.hom ≫ G.map ν.hom.left ≫
        t.obj.left.iso.inv ≫ F.map t.obj.hom := (Iso.inv_comp_eq _).mp hν.symm
    have hw : F.map (s.obj.hom ≫ CategoryTheory.inv t.obj.hom) ≫ t.obj.left.iso.hom =
        s.obj.left.iso.hom ≫ G.map ν.hom.left := by
      rw [F.map_comp, Category.assoc, h₁, Functor.map_inv]
      simp only [Category.assoc, IsIso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
    have hfac : (CategoricalPullback.π₁ F G).map
        (CategoricalPullback.Hom.mk (s.obj.hom ≫ CategoryTheory.inv t.obj.hom)
          ν.hom.left hw) ≫ t.obj.hom = s.obj.hom := by
      show (s.obj.hom ≫ CategoryTheory.inv t.obj.hom) ≫ t.obj.hom = s.obj.hom
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    refine ⟨ObjectProperty.homMk (CostructuredArrow.homMk
      (CategoricalPullback.Hom.mk (s.obj.hom ≫ CategoryTheory.inv t.obj.hom)
        ν.hom.left hw) hfac), ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ rfl)⟩

/-- The comparison hits every lift of `F x` across `G`: the point with first component `x`
and structural isomorphism the inverse of the given arrow. -/
public theorem categoricalPullbackIsoFiberRestrict_surjective :
    Function.Surjective (categoricalPullbackIsoFiberRestrict F G x).obj := by
  intro u
  have hu : IsIso u.obj.hom := u.property
  refine ⟨⟨(⟨⟨x, u.obj.left, (asIso u.obj.hom).symm⟩, ⟨⟨⟩⟩, 𝟙 x⟩ :
      CostructuredArrow (CategoricalPullback.π₁ F G) x),
    show IsIso (𝟙 x) from inferInstance⟩, ?_⟩
  refine IsoFiber.ext rfl (heq_of_eq ?_)
  show u.obj.hom ≫ F.map (𝟙 x) = u.obj.hom
  rw [F.map_id, Category.comp_id]

/-- **Lifts across a categorical pullback square.** The lifts of `x` across the first
projection of a categorical pullback are, up to isomorphism, the lifts of `F x` across the
second leg of the cospan. -/
public theorem categoricalPullbackIsoFiberRestrict_isEquivalence :
    (categoricalPullbackIsoFiberRestrict F G x).IsEquivalence := by
  have := categoricalPullbackIsoFiberRestrict_full F G x
  have := categoricalPullbackIsoFiberRestrict_faithful F G x
  have := Functor.essSurj_of_surj (categoricalPullbackIsoFiberRestrict_surjective F G x)
  exact {}

end CategoricalPullbackLift

/-! ### Iso-fibres and precomposition with an equivalence -/

section IsoFiberPrecomp

open CategoryTheory.Functor

variable {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]

/-- A fully faithful and essentially surjective functor induces a bijection on isomorphism
classes. -/
public theorem isoClassMap_bijective_of_essSurj {E F : Type*} [Category E] [Category F]
    (G : E ⥤ F) [G.Full] [G.Faithful] [G.EssSurj] :
    Function.Bijective (isoClassMap G) := by
  constructor
  · intro a b
    induction a using Quotient.ind with
    | _ a =>
      induction b using Quotient.ind with
      | _ b =>
        intro hab
        obtain ⟨e⟩ := Quotient.exact hab
        exact Quotient.sound ⟨G.preimageIso e⟩
  · intro a
    induction a using Quotient.ind with
    | _ a => exact ⟨Quotient.mk _ (G.objPreimage a), Quotient.sound ⟨G.objObjPreimageIso a⟩⟩

/-- Precomposition with an equivalence identifies iso-fibres: a lift of `x` across a functor
is a lift of `x` across the functor it factors through. -/
public def isoFiberPrecompEquivalence (E : C₁ ⥤ C₂) [E.IsEquivalence] (K : C₂ ⥤ C₃)
    {L : C₁ ⥤ C₃} (α : E ⋙ K ≅ L) (x : C₃) :
    IsoFiber L x ≌ IsoFiber K x := by
  let α' : E ⋙ K ≅ L ⋙ 𝟭 C₃ := α ≪≫ L.rightUnitor.symm
  let : IsIso α'.hom := α'.isIso_hom
  let : IsIso (𝟙 x) := inferInstance
  let A₀ : CostructuredArrow L x ⥤ CostructuredArrow K x :=
    CostructuredArrow.map₂ (S := L) (T := x) (U := K) (V := x) (F := E) (G := 𝟭 _)
      α'.hom (𝟙 x)
  let : A₀.IsEquivalence := by
    change (CostructuredArrow.map₂ α'.hom (𝟙 x)).IsEquivalence
    infer_instance
  have hA₀ : (IsIsoCostructuredArrow K x).inverseImage A₀.asEquivalence.functor =
      IsIsoCostructuredArrow L x := by
    ext t
    change IsIso (A₀.obj t).hom ↔ IsIso t.hom
    have he : (A₀.obj t).hom = α'.hom.app t.left ≫ t.hom := by
      change α'.hom.app t.left ≫ (𝟭 C₃).map t.hom ≫ 𝟙 x = α'.hom.app t.left ≫ t.hom
      simp
    have hα : IsIso (α'.hom.app t.left) := inferInstance
    rw [he]
    exact ⟨fun _ => IsIso.of_isIso_comp_left (α'.hom.app t.left) t.hom,
      fun _ => inferInstance⟩
  exact A₀.asEquivalence.congrFullSubcategory hA₀

end IsoFiberPrecomp

/-! ### Lifts across an (RS*) square -/

section SquareLift

open CategoryTheory.Limits CategoryTheory.Functor

variable {C : Type*} [Category C] {D : Type*} [Category D] (p : D ⥤ C)
  (c : p.ChoiceOfPullbacks) {U V W Z : C} (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z)
  (h : f ≫ i = g ≫ j)

/-- The comparison functor of a commutative square, followed by the first projection of the
categorical pullback, is restriction along the arrow into the fourth corner. -/
public theorem fiberSquareComparison_comp_π₁ :
    fiberSquareComparison p c f g i j h ⋙
        CategoricalPullback.π₁ (c.pullbackFunctor f) (c.pullbackFunctor g) =
      c.pullbackFunctor i :=
  rfl

/-- **(RS*) on lifts.** When the comparison functor of a commutative square is an
equivalence, a lift of an object `x` of the fibre over the second corner along the arrow into
the fourth corner is the same thing as a lift of the restriction of `x` to the first corner
along the other branch of the square. -/
public def squareLiftEquivalence
    (hE : (fiberSquareComparison p c f g i j h).IsEquivalence) (x : p.Fiber V) :
    IsoFiber (c.pullbackFunctor i) x ≌
      IsoFiber (c.pullbackFunctor g) ((c.pullbackFunctor f).obj x) :=
  letI := hE
  letI := categoricalPullbackIsoFiberRestrict_isEquivalence
    (c.pullbackFunctor f) (c.pullbackFunctor g) x
  (isoFiberPrecompEquivalence (fiberSquareComparison p c f g i j h) _
      (eqToIso (fiberSquareComparison_comp_π₁ p c f g i j h)) x).trans
    (categoricalPullbackIsoFiberRestrict (c.pullbackFunctor f) (c.pullbackFunctor g)
      x).asEquivalence

/-- **(RS*) on isomorphism classes of lifts.** The lift classes of `x` along the arrow into
the fourth corner of a commutative square whose comparison functor is an equivalence are the
lift classes of the restriction of `x` to the first corner along the other branch. -/
public def squareLiftClassesEquiv (hp : p.IsFiberedInGroupoids)
    (hE : (fiberSquareComparison p c f g i j h).IsEquivalence) (x : p.Fiber V) :
    Quotient (isIsomorphicSetoid ((Under.post p).Fiber (Under.mk (eqToHom x.2 ≫ i)))) ≃
      Quotient (isIsomorphicSetoid ((Under.post p).Fiber
        (Under.mk (eqToHom ((c.pullbackFunctor f).obj x).2 ≫ g)))) :=
  (isoFiberUnderClassesEquiv p hp c i x).symm.trans
    ((Equiv.ofBijective _ (isoClassMap_bijective_of_essSurj
        (squareLiftEquivalence p c f g i j h hE x).functor)).trans
      (isoFiberUnderClassesEquiv p hp c g ((c.pullbackFunctor f).obj x)))

end SquareLift

/-! ### The square `A[M] = A ×_{A'} A'[N]` -/

section BaseChangeSquare

open CategoryTheory.Limits

variable {A A' : Type u} [CommRing A] [CommRing A'] (f : A →+* A')
  {M : ModuleCat.{u} A} {N : ModuleCat.{u} A'}

/-- A morphism of modules into a restriction of scalars, read as a map of the underlying
additive groups. -/
public abbrev restrictScalarsAddHom (ψ : M ⟶ (ModuleCat.restrictScalars f).obj N) :
    (M : Type u) →+ (N : Type u) :=
  ψ.hom.toAddMonoidHom

/-- A morphism of modules into a restriction of scalars is semilinear over the ring map. -/
public theorem restrictScalarsAddHom_smul (ψ : M ⟶ (ModuleCat.restrictScalars f).obj N)
    (a : A) (m : M) :
    restrictScalarsAddHom f ψ (a • m) = f a • restrictScalarsAddHom f ψ m :=
  ψ.hom.map_smul a m

variable (ψ : (M : Type u) →+ (N : Type u))
  (hψ : ∀ (a : A) (m : M), ψ (a • m) = f a • ψ m)

include hψ in
/-- The ring map `A[M] ⟶ A'[N]` of trivial square-zero extensions determined by a ring map
`f : A ⟶ A'` and an `f`-semilinear map `M ⟶ N` of coefficients. -/
public def squareZeroRingBaseMap : TrivSqZeroExt A M →+* TrivSqZeroExt A' N where
  toFun z := (f z.fst, ψ z.snd)
  map_one' := TrivSqZeroExt.ext f.map_one ψ.map_zero
  map_zero' := TrivSqZeroExt.ext f.map_zero ψ.map_zero
  map_add' z z' := TrivSqZeroExt.ext (f.map_add z.fst z'.fst) (ψ.map_add z.snd z'.snd)
  map_mul' z z' :=
    TrivSqZeroExt.ext (f.map_mul z.fst z'.fst) (by
      change ψ (z.fst • z'.snd + MulOpposite.op z'.fst • z.snd) =
        f z.fst • ψ z'.snd + MulOpposite.op (f z'.fst) • ψ z.snd
      rw [op_smul_eq_smul, op_smul_eq_smul, map_add, hψ, hψ])

include hψ in
/-- The map of square-zero extensions induced by a semilinear map of coefficients is the pair
of the ring map and the semilinear map. -/
public theorem squareZeroRingBaseMap_apply (z : TrivSqZeroExt A M) :
    squareZeroRingBaseMap f ψ hψ z = (f z.fst, ψ z.snd) :=
  rfl

include hψ in
/-- **The square `A[M] = A ×_{A'} A'[N]`.** For a ring map `f : A ⟶ A'` and an `f`-semilinear
bijection `M ⟶ N` of coefficients, the trivial square-zero extension `A[M]` is the fibre
product of `A` and `A'[N]` over `A'`. The orientation is the one in which the (RS*) condition
reads a square: the pullback corner is `A[M]`, and the square-zero surjection is the
projection `A'[N] ⟶ A'` appearing as the fourth map. -/
public theorem squareZeroRingBaseMap_isPullback (hbij : Function.Bijective ψ) :
    IsPullback (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A M).toRingHom)
      (CommRingCat.ofHom (squareZeroRingBaseMap f ψ hψ)) (CommRingCat.ofHom f)
      (CommRingCat.ofHom (TrivSqZeroExt.fstHom A' A' N).toRingHom) := by
  apply IsPullback.of_map_of_faithful (forget CommRingCat)
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨?_, ?_, ?_⟩
  · ext z
    show f z.fst = (squareZeroRingBaseMap f ψ hψ z).fst
    rfl
  · intro a b hab
    change TrivSqZeroExt.fst a = TrivSqZeroExt.fst b ∧
      squareZeroRingBaseMap f ψ hψ a = squareZeroRingBaseMap f ψ hψ b at hab
    exact TrivSqZeroExt.ext hab.1 (hbij.1 (congrArg TrivSqZeroExt.snd hab.2))
  · intro a b hab
    change f a = TrivSqZeroExt.fst b at hab
    obtain ⟨m, hm⟩ := hbij.2 b.snd
    refine ⟨(a, m), rfl, ?_⟩
    show squareZeroRingBaseMap f ψ hψ (a, m) = b
    exact TrivSqZeroExt.ext hab hm

end BaseChangeSquare

/-! ### The square `A[M] = A ×_{A'} A'[N]` in the site -/

section BaseChangeSquareSite

open CategoryTheory.Limits

variable {A A' : Type u} [CommRing A] [CommRing A'] (f : A →+* A')
  (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (toS' : Spec (.of A') ⟶ S)
  (hA : B.Contains (Spec (.of A))) (hA' : B.Contains (Spec (.of A')))
  (hf : Spec.map (CommRingCat.ofHom f) ≫ toS = toS')
  (M : SiteModule A B) (N : SiteModule A' B)
  (ψ : (M.obj : Type u) →+ (N.obj : Type u))
  (hψ : ∀ (a : A) (m : M.obj), ψ (a • m) = f a • ψ m)

/-- The global sections of a surjection of affine schemes coming from a surjection of rings
form a surjection. -/
public theorem surjective_specMap_appTop {R T : CommRingCat.{u}} (φ : R ⟶ T)
    (hφ : Function.Surjective φ) : Function.Surjective (Spec.map φ).appTop.hom :=
  have : IsClosedImmersion (Spec.map φ) := IsClosedImmersion.spec_of_surjective φ hφ
  (Spec.map φ).app_surjective ⊤ (isAffineOpen_top _)

include hf in
/-- The morphism `Spec A' ⟶ Spec A` of objects of the site over `S` attached to a ring map
`A ⟶ A'` compatible with the structure morphisms.

Named `...OfRingHom` to distinguish it from `Deformation.Artin.algebraOverMapOfRingHom` in
`StacksFrontier.Deformation.Artin.Infinitesimal.FlatBaseChange`: that version is parameterised
by an `Algebra A C` instance and takes the compatibility for `algebraMap A C`, whereas this
one takes a bare ring map `f`, so the two are not interchangeable. -/
public def algebraOverMapOfRingHom :
    algebraOver A' B S hS toS' hA' ⟶ algebraOver A B S hS toS hA := by
  refine Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom f)) :
    B.obj hA' ⟶ B.obj hA) ?_
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom f) ≫ toS = toS'
  exact hf

include hf hψ in
/-- The morphism `Spec A'[N] ⟶ Spec A[M]` of objects of the site over `S` attached to a ring
map `A ⟶ A'` and an `f`-semilinear map of coefficients. -/
public def squareZeroOverBaseMap :
    squareZeroOver A' B S hS toS' N ⟶ squareZeroOver A B S hS toS M := by
  refine Over.homMk (ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom (squareZeroRingBaseMap f ψ hψ))) :
      B.obj N.property ⟶ B.obj M.property) ?_
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom (squareZeroRingBaseMap f ψ hψ)) ≫
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom A M.obj)) ≫ toS =
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom A' N.obj)) ≫ toS'
  have hinl : CommRingCat.ofHom (TrivSqZeroExt.inlHom A M.obj) ≫
      CommRingCat.ofHom (squareZeroRingBaseMap f ψ hψ) =
        CommRingCat.ofHom f ≫ CommRingCat.ofHom (TrivSqZeroExt.inlHom A' N.obj) := by
    apply CommRingCat.hom_ext
    ext a
    · rfl
    · change ψ (TrivSqZeroExt.inl a).snd = (TrivSqZeroExt.inl (f a)).snd
      rw [TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inl, ψ.map_zero]
  rw [← Category.assoc, ← Spec.map_comp, hinl, Spec.map_comp, Category.assoc, hf]

include hf hψ in
/-- The morphism `squareZeroOverBaseMap` is the morphism of spectra determined by
`squareZeroRingBaseMap`. -/
public theorem squareZeroOverBaseMap_spec :
    (BigFppfOver.toScheme B S hS).map (squareZeroOverBaseMap f B S hS toS toS' hf M N ψ hψ) =
      Spec.map (CommRingCat.ofHom (squareZeroRingBaseMap f ψ hψ)) :=
  rfl

include hf hψ in
/-- The morphism of spectra determined by composing `squareZeroOverBaseMap` with a further
morphism of the site over `S` out of `squareZeroOver A B S hS toS M`, expressed through the
ring map that this further morphism is already known to be. Stated with the composition kept
inside this section (so that the coefficient module `M.obj` carries a single, consistently
resolved `CommRing (TrivSqZeroExt A M.obj)` instance throughout) in order to avoid a residual
instance-diamond that a direct `Spec.map_comp`/`CommRingCat.ofHom_comp` rewrite at the call
site would otherwise hit. -/
public theorem squareZeroOverBaseMap_comp_spec
    (h : squareZeroOver A B S hS toS M ⟶ algebraOver A B S hS toS hA)
    (r : A →+* TrivSqZeroExt A (M.obj : Type u))
    (hr : (BigFppfOver.toScheme B S hS).map h = Spec.map (CommRingCat.ofHom r)) :
    (BigFppfOver.toScheme B S hS).map (squareZeroOverBaseMap f B S hS toS toS' hf M N ψ hψ ≫ h) =
      Spec.map (CommRingCat.ofHom ((squareZeroRingBaseMap f ψ hψ).comp r)) := by
  rw [(BigFppfOver.toScheme B S hS).map_comp,
    squareZeroOverBaseMap_spec f B S hS toS toS' hf M N ψ hψ, hr]
  exact (Spec.map_comp (CommRingCat.ofHom r)
      (CommRingCat.ofHom (squareZeroRingBaseMap f ψ hψ))).symm.trans
    (congrArg Spec.map (CommRingCat.ofHom_comp r (squareZeroRingBaseMap f ψ hψ)).symm)

include hf hψ in
/-- The two square-zero immersions and the two maps induced by `A ⟶ A'` form a commutative
square of objects of the site over `S`. -/
public theorem algebraOverMap_comp_squareZeroArrow :
    algebraOverMapOfRingHom f B S hS toS toS' hA hA' hf ≫ squareZeroArrow A B S hS toS hA M =
      squareZeroArrow A' B S hS toS' hA' N ≫
        squareZeroOverBaseMap f B S hS toS toS' hf M N ψ hψ := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  show Spec.map (CommRingCat.ofHom f) ≫
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A M.obj).toRingHom) =
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A' A' N.obj).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (squareZeroRingBaseMap f ψ hψ))
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

include hf hψ in
/-- **(RS*) at the square `A[M] = A ×_{A'} A'[N]`.** For a ring map `A ⟶ A'` and an
`f`-semilinear bijection of coefficients, restriction along the two legs is an equivalence
from the fibre over `Spec A[M]` to the two-fibre product of the fibres over `Spec A`,
`Spec A'[N]` and `Spec A'`. -/
public theorem baseChangeSquare_isEquivalence {X : Type v} [Category.{w} X]
    (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSStar B S hS p hp) (hbij : Function.Bijective ψ) :
    letI : p.IsFibered := hp.isFibered
    (fiberSquareComparison p (Functor.chosenPullbacks p)
      (algebraOverMapOfRingHom f B S hS toS toS' hA hA' hf)
      (squareZeroArrow A' B S hS toS' hA' N)
      (squareZeroArrow A B S hS toS hA M)
      (squareZeroOverBaseMap f B S hS toS toS' hf M N ψ hψ)
      (algebraOverMap_comp_squareZeroArrow f B S hS toS toS' hA hA' hf M N
        ψ hψ)).IsEquivalence := by
  let : p.IsFibered := hp.isFibered
  let U : BigAffineFppf B S hS :=
    ⟨algebraOver A' B S hS toS' hA', show IsAffine (Spec (.of A')) from inferInstance⟩
  let V : BigAffineFppf B S hS :=
    ⟨algebraOver A B S hS toS hA, show IsAffine (Spec (.of A)) from inferInstance⟩
  let W : BigAffineFppf B S hS :=
    ⟨squareZeroOver A' B S hS toS' N,
      show IsAffine (Spec (squareZeroRing A' N.obj)) from inferInstance⟩
  let Z : BigAffineFppf B S hS :=
    ⟨squareZeroOver A B S hS toS M,
      show IsAffine (Spec (squareZeroRing A M.obj)) from inferInstance⟩
  let fa : U ⟶ V := ObjectProperty.homMk (algebraOverMapOfRingHom f B S hS toS toS' hA hA' hf)
  let ga : U ⟶ W := ObjectProperty.homMk (squareZeroArrow A' B S hS toS' hA' N)
  let ia : V ⟶ Z := ObjectProperty.homMk (squareZeroArrow A B S hS toS hA M)
  let ja : W ⟶ Z :=
    ObjectProperty.homMk (squareZeroOverBaseMap f B S hS toS toS' hf M N ψ hψ)
  have hcomm : fa ≫ ia = ga ≫ ja :=
    ObjectProperty.hom_ext _
      (algebraOverMap_comp_squareZeroArrow f B S hS toS toS' hA hA' hf M N ψ hψ)
  have hpb : IsPullback ((BigAffineFppf.toScheme B S hS).map ia).appTop
      ((BigAffineFppf.toScheme B S hS).map ja).appTop
      ((BigAffineFppf.toScheme B S hS).map fa).appTop
      ((BigAffineFppf.toScheme B S hS).map ga).appTop := by
    apply (squareZeroRingBaseMap_isPullback f ψ hψ hbij).of_iso'
      (Scheme.ΓSpecIso _) (Scheme.ΓSpecIso _) (Scheme.ΓSpecIso _) (Scheme.ΓSpecIso _)
    · exact (Scheme.ΓSpecIso_naturality
        (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A M.obj).toRingHom)).symm
    · exact (Scheme.ΓSpecIso_naturality
        (CommRingCat.ofHom (squareZeroRingBaseMap f ψ hψ))).symm
    · exact (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f)).symm
    · exact (Scheme.ΓSpecIso_naturality
        (CommRingCat.ofHom (TrivSqZeroExt.fstHom A' A' N.obj).toRingHom)).symm
  have hsurj : Function.Surjective
      ((BigAffineFppf.toScheme B S hS).map ga).appTop.hom :=
    surjective_specMap_appTop
      (CommRingCat.ofHom (TrivSqZeroExt.fstHom A' A' N.obj).toRingHom)
      (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩)
  have hker : RingHom.ker (CommRingCat.ofHom
      (TrivSqZeroExt.fstHom A' A' N.obj).toRingHom).hom ^ 2 = ⊥ := by
    refine le_antisymm ?_ bot_le
    rw [pow_two, Ideal.mul_le]
    intro a ha b hb
    change a.fst = 0 at ha
    change b.fst = 0 at hb
    show (a * b : TrivSqZeroExt A' N.obj) = 0
    refine TrivSqZeroExt.ext ?_ ?_
    · show a.fst * b.fst = 0
      rw [ha, zero_mul]
    · show a.fst • b.snd + MulOpposite.op b.fst • a.snd = 0
      rw [ha, hb]
      simp
  have hsq : RingHom.ker ((BigAffineFppf.toScheme B S hS).map ga).appTop.hom ^ 2 = ⊥ :=
    Stacks.Smooth.ker_specMap_appTop_pow_eq_bot _ hker
  exact hRS U V W Z fa ga ia ja hcomm hpb hsurj hsq

include hf hψ in
/-- **(RS*) on lift classes over `A[M]`.** For a ring map `A ⟶ A'` and an `f`-semilinear
bijection `M ⟶ N` of coefficients, the isomorphism classes of lifts of `x` over `Spec A[M]`
are the isomorphism classes of lifts of the restriction of `x` to `Spec A'` over
`Spec A'[N]`. This is the Rim–Schlessinger input `Lift(x, A[M]) = Lift(x|_{Spec A'}, A'[N])`
of Stacks 07YT. -/
public def baseChangeLiftClassesEquiv {X : Type v} [Category.{w} X]
    (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSStar B S hS p hp) (hbij : Function.Bijective ψ)
    (x : X) (hx : p.obj x = algebraOver A B S hS toS hA) :
    letI : p.IsFibered := hp.isFibered
    squareZeroLiftClasses A B S hS toS hA p x hx M ≃
      squareZeroLiftClasses A' B S hS toS' hA' p
        (((Functor.chosenPullbacks p).pullbackFunctor
          (algebraOverMapOfRingHom f B S hS toS toS' hA hA' hf)).obj ⟨x, hx⟩).1
        (((Functor.chosenPullbacks p).pullbackFunctor
          (algebraOverMapOfRingHom f B S hS toS toS' hA hA' hf)).obj ⟨x, hx⟩).2 N :=
  letI : p.IsFibered := hp.isFibered
  squareLiftClassesEquiv p (Functor.chosenPullbacks p)
    (algebraOverMapOfRingHom f B S hS toS toS' hA hA' hf)
    (squareZeroArrow A' B S hS toS' hA' N)
    (squareZeroArrow A B S hS toS hA M)
    (squareZeroOverBaseMap f B S hS toS toS' hf M N ψ hψ)
    (algebraOverMap_comp_squareZeroArrow f B S hS toS toS' hA hA' hf M N ψ hψ) hp
    (baseChangeSquare_isEquivalence f B S hS toS toS' hA hA' hf M N ψ hψ p hp hRS hbij)
    ⟨x, hx⟩

end BaseChangeSquareSite

end Deformation.Artin

end
