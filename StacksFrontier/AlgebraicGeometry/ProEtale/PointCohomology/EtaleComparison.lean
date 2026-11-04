module

public import StacksFrontier.AlgebraicGeometry.ProEtale.PointCohomology.EtaleApproximation

/-!
# The pro-étale sheaf of a discrete Galois module

For a field `K` and a discrete Galois module `N`, the pullback along the morphism from the
pro-étale site of `Spec K` to its étale site of the étale sheaf attached to `N` is the sheaf of
locally constant equivariant functions on geometric points with values in `N`.

## Main definitions

* `discSheaf`: The pro-étale sheaf of locally constant equivariant functions on geometric points
  with values in a discrete Galois module.
* `discSheafFunctor`: The construction `discSheaf`, functorially in the Galois module.
* `epsDirect`: The direct image from pro-étale to étale module sheaves.

## Main results

* `W_counit_discSheaf`: The counit of the left Kan extension along the inclusion of the étale
  site, at the discrete sheaf of a Galois module, becomes an isomorphism after sheafification.
* `proetaleSheafIsoDisc`: The pro-étale sheaf of a discrete Galois module is isomorphic to the
  sheaf of locally constant equivariant functions on geometric points, naturally in the module.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology

universe u r w

namespace AlgebraicGeometry.GaloisSheaf

variable {K : Type u} [Field K] (Λ : Type r) [Ring Λ]

private theorem smallSiteWEqualsLocallyBijective_moduleCat {D : Type (max w r)}
    [SmallCategory D] (J : GrothendieckTopology D) (R : Type r) [Ring R] :
    J.WEqualsLocallyBijective (ModuleCat.{max w r} R) := by
  have : HasSheafify J (ModuleCat.{max w r} R) :=
    hasSheafify_moduleCat.{max w r, max w r, max w r, r} J R
  infer_instance

/-- On the small pro-étale site of `Spec K`, a morphism of presheaves of modules becomes an
isomorphism after sheafification if and only if it is locally bijective. -/
theorem proEt_wEqualsLocallyBijective :
    (Scheme.ProEt.topology (base K)).WEqualsLocallyBijective (ModuleCat.{max (u + 1) r w} Λ) := by
  have := smallSiteWEqualsLocallyBijective_moduleCat.{r, max (u + 1) w}
    ((equivSmallModel.{max (u + 1) r w} (base K).ProEt).inverse.inducedTopology
      (Scheme.ProEt.topology (base K))) Λ
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, _, u + 1, _,
    max (u + 1) r w} _

/-! ### The sheaf attached to a discrete Galois module -/

variable {Λ}

/-- The pro-étale sheaf of locally constant equivariant functions on geometric points with
values in a discrete Galois module. -/
def discSheaf (N : Rep.{w} Λ (galoisGroup K)) :
    Sheaf (Scheme.ProEt.topology (base K)) (ModuleCat.{max (u + 1) r w} Λ) :=
  letI : TopologicalSpace N := ⊥
  haveI : DiscreteTopology N := ⟨rfl⟩
  haveI : ContinuousConstSMul Λ N := ⟨fun _ ↦ continuous_of_discreteTopology⟩
  contSheaf Λ N.ρ

variable (Λ) in
/-- The sheaf of locally constant equivariant functions, functorially in the discrete Galois
module. -/
def discSheafFunctor : Rep.{w} Λ (galoisGroup K) ⥤
    Sheaf (Scheme.ProEt.topology (base K)) (ModuleCat.{max (u + 1) r w} Λ) where
  obj := discSheaf
  map {N N'} f :=
    letI : TopologicalSpace N := ⊥
    haveI : DiscreteTopology N := ⟨rfl⟩
    haveI : ContinuousConstSMul Λ N := ⟨fun _ ↦ continuous_of_discreteTopology⟩
    letI : TopologicalSpace N' := ⊥
    haveI : DiscreteTopology N' := ⟨rfl⟩
    haveI : ContinuousConstSMul Λ N' := ⟨fun _ ↦ continuous_of_discreteTopology⟩
    contSheafMap f.hom.toLinearMap continuous_of_discreteTopology (Rep.hom_comm_apply f)
  map_id _ := rfl
  map_comp _ _ := rfl

/-! ### On the étale site the discrete sheaf is the sheaf of the Galois module -/

/-- On an étale object every equivariant function on geometric points is a section of the
discrete sheaf: geometric points of an object of finite type are discrete on affine objects. -/
lemma mem_contSections_of_etale (N : Rep.{w} Λ (galoisGroup K)) (U : (base K).Etale)
    (f : GeomPt K ((base K).etaleToProetale.obj U) → N)
    (hf : ∀ (g : galoisGroup K) φ, f (g • φ) = N.ρ g (f φ)) :
    letI : TopologicalSpace N := ⊥
    haveI : DiscreteTopology N := ⟨rfl⟩
    haveI : ContinuousConstSMul Λ N := ⟨fun _ ↦ continuous_of_discreteTopology⟩
    f ∈ contSections Λ N.ρ ((base K).etaleToProetale.obj U) := by
  let : TopologicalSpace N := ⊥
  have : DiscreteTopology N := ⟨rfl⟩
  have : ContinuousConstSMul Λ N := ⟨fun _ ↦ continuous_of_discreteTopology⟩
  refine ⟨hf, fun A a hA ↦ ?_⟩
  have := hA
  have : Etale (GeomPt.strHom ((base K).etaleToProetale.obj U)) := U.prop
  exact GeomPt.continuous_comp_map_of_locallyOfFiniteType a f

variable (Λ) in
/-- **On the étale site the discrete sheaf is the presheaf of equivariant functions.** -/
def presheafFunctorIsoDisc : presheafFunctor K Λ ≅ discSheafFunctor Λ ⋙
    sheafToPresheaf (Scheme.ProEt.topology (base K)) (ModuleCat.{max (u + 1) r w} Λ) ⋙
      (Functor.whiskeringLeft _ _ _).obj (base K).etaleToProetale.op :=
  NatIso.ofComponents (fun N ↦ NatIso.ofComponents (fun U ↦ LinearEquiv.toModuleIso
    { toFun a := ⟨⟨a.down.1, mem_contSections_of_etale N U.unop a.down.1 a.down.2⟩⟩
      invFun b := ⟨⟨b.down.1, b.down.2.1⟩⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      left_inv _ := rfl
      right_inv _ := rfl }) (fun _ ↦ rfl)) (fun _ ↦ rfl)

/-! ### Elements of the left Kan extension along the inclusion of the étale site -/

variable (K) in
/-- The inclusion of the small étale site of `Spec K` into its small pro-étale site. -/
abbrev etaleInc : (base K).Etale ⥤ (base K).ProEt := (base K).etaleToProetale

section LanElements

variable (Q : (base K).ProEtᵒᵖ ⥤ ModuleCat.{max (u + 1) r w} Λ)

/-- The section of the left Kan extension over `V` given by a section over an étale object `W`
and a morphism `V ⟶ W`. -/
def lanElt {V : (base K).ProEt} (W : (base K).Etale) (h : V ⟶ (etaleInc K).obj W)
    (x : Q.obj (op ((etaleInc K).obj W))) :
    ((etaleInc K).op.lan.obj ((etaleInc K).op ⋙ Q)).obj (op V) :=
  (((etaleInc K).op.lan.obj ((etaleInc K).op ⋙ Q)).map h.op).hom
    ((((etaleInc K).op.lanUnit.app ((etaleInc K).op ⋙ Q)).app (op W)).hom x)

/-- Restricting `lanElt Q W h x` along `g : V' ⟶ V` gives `lanElt Q W (g ≫ h) x`. -/
lemma lanElt_map {V V' : (base K).ProEt} (g : V' ⟶ V) (W : (base K).Etale)
    (h : V ⟶ (etaleInc K).obj W) (x : Q.obj (op ((etaleInc K).obj W))) :
    (((etaleInc K).op.lan.obj ((etaleInc K).op ⋙ Q)).map g.op).hom (lanElt Q W h x) =
      lanElt Q W (g ≫ h) x := by
  simp only [lanElt, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- For a morphism `k : W' ⟶ W` of étale objects, `lanElt Q W (h ≫ (etaleInc K).map k) x` is
`lanElt Q W' h` applied to the restriction of `x` along `k`. -/
lemma lanElt_comp {V : (base K).ProEt} {W W' : (base K).Etale} (k : W' ⟶ W)
    (h : V ⟶ (etaleInc K).obj W') (x : Q.obj (op ((etaleInc K).obj W))) :
    lanElt Q W (h ≫ (etaleInc K).map k) x =
      lanElt Q W' h ((Q.map ((etaleInc K).map k).op).hom x) := by
  simp only [lanElt, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact congrArg _ (NatTrans.naturality_apply ((etaleInc K).op.lanUnit.app ((etaleInc K).op ⋙ Q))
    k.op x).symm

/-- The counit of the left Kan extension sends `lanElt Q W h x` to the restriction of `x` along
`h`. -/
lemma counit_lanElt {V : (base K).ProEt} (W : (base K).Etale) (h : V ⟶ (etaleInc K).obj W)
    (x : Q.obj (op ((etaleInc K).obj W))) :
    ((((etaleInc K).op.lanAdjunction _).counit.app Q).app (op V)).hom (lanElt Q W h x) =
      (Q.map h.op).hom x := by
  have h1 := NatTrans.naturality_apply (((etaleInc K).op.lanAdjunction _).counit.app Q) h.op
    ((((etaleInc K).op.lanUnit.app ((etaleInc K).op ⋙ Q)).app (op W)).hom x)
  have h2 := congrArg (fun φ ↦ φ.hom x)
    ((etaleInc K).op.lanUnit_app_app_lanAdjunction_counit_app_app Q (op W))
  exact h1.trans (congrArg (Q.map h.op).hom h2)

/-- The category of étale objects under a pro-étale object `V`, viewed as costructured arrows
for the opposite inclusion, is filtered. -/
instance isFiltered_costructuredArrow (V : (base K).ProEt) :
    IsFiltered (CostructuredArrow (etaleInc K).op (op V)) :=
  have : RepresentablyFlat (etaleInc K) := flat_of_preservesFiniteLimits _
  IsFiltered.of_equivalence (structuredArrowOpEquivalence (etaleInc K) V)

/-- Every section of the left Kan extension comes from a single étale object. -/
lemma exists_lanElt {V : (base K).ProEt}
    (z : ((etaleInc K).op.lan.obj ((etaleInc K).op ⋙ Q)).obj (op V)) :
    ∃ (W : (base K).Etale) (h : V ⟶ (etaleInc K).obj W) (x : Q.obj (op ((etaleInc K).obj W))),
      z = lanElt Q W h x := by
  let e := (etaleInc K).op.leftKanExtensionObjIsoColimit ((etaleInc K).op ⋙ Q) (op V)
  have : PreservesColimitsOfSize.{max (u + 1) r w, max (u + 1) r w}
      (forget₂ (ModuleCat.{max (u + 1) r w} Λ) AddCommGrpCat.{max (u + 1) r w}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{max (u + 1) r w, r, max (u + 1) r w,
      max (u + 1) r w} Λ
  have : PreservesFilteredColimits (forget (ModuleCat.{max (u + 1) r w} Λ)) :=
    comp_preservesFilteredColimits.{max (u + 1) r w, max (u + 1) r w}
      (forget₂ (ModuleCat.{max (u + 1) r w} Λ) AddCommGrpCat.{max (u + 1) r w})
      (forget AddCommGrpCat.{max (u + 1) r w})
  have : PreservesFilteredColimitsOfSize.{u, u + 1} (forget (ModuleCat.{max (u + 1) r w} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u + 1, max (u + 1) r w, u, max (u + 1) r w} _
  obtain ⟨j, y, hy⟩ := Concrete.colimit_exists_rep
    (CostructuredArrow.proj (etaleInc K).op (op V) ⋙ ((etaleInc K).op ⋙ Q)) (e.hom.hom z)
  refine ⟨j.left.unop, j.hom.unop, y, ?_⟩
  have h := congrArg (fun φ ↦ φ.hom y)
    ((etaleInc K).op.ι_leftKanExtensionObjIsoColimit_inv ((etaleInc K).op ⋙ Q) (op V) j)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  have hz : e.inv.hom (e.hom.hom z) = z := congrArg (fun φ ↦ φ.hom z) e.hom_inv_id
  rwa [← hz, ← hy]

end LanElements

/-! ### The counit of the left Kan extension is locally bijective on the discrete sheaf -/

section Counit

variable (N : Rep.{w} Λ (galoisGroup K))

/-- On an affine object every section of the discrete sheaf comes from an étale object. -/
lemma exists_lanElt_counit_eq {A : (base K).ProEt} [IsAffine A.left]
    (s : (discSheaf N).obj.obj (op A)) :
    ∃ (W : (base K).Etale) (h : A ⟶ (etaleInc K).obj W)
      (x : (discSheaf N).obj.obj (op ((etaleInc K).obj W))),
      ((((etaleInc K).op.lanAdjunction _).counit.app (discSheaf N).obj).app (op A)).hom
        (lanElt (discSheaf N).obj W h x) = s := by
  let : TopologicalSpace N := ⊥
  have : DiscreteTopology N := ⟨rfl⟩
  have : ContinuousConstSMul Λ N := ⟨fun _ ↦ continuous_of_discreteTopology⟩
  let f : GeomPt K A → N := s.down.1
  have hfc : Continuous f := by
    have := s.down.2.2 A (𝟙 A) ‹_›
    rwa [show s.down.1 ∘ GeomPt.map (𝟙 A) = s.down.1 from funext fun φ ↦ by simp] at this
  obtain ⟨B, hB, hfac⟩ :=
    GeomPt.exists_fg_factor f ((IsLocallyConstant.iff_continuous f).2 hfc)
  have := etale_of_fg A B hB
  have hsurj := GeomPt.map_toSpecSub_surjective (V := A) B
  let t : GeomPt K (specProObj B) → N := fun ψ ↦ f (hsurj ψ).choose
  have ht : ∀ φ, t (GeomPt.map (toSpecSub A B) φ) = f φ := fun φ ↦
    hfac _ _ (hsurj _).choose_spec
  have hteq : ∀ (g : galoisGroup K) ψ, t (g • ψ) = N.ρ g (t ψ) := by
    intro g ψ
    obtain ⟨φ, rfl⟩ := hsurj ψ
    rw [← GeomPt.map_smul, ht, ht]
    exact s.down.2.1 g φ
  exact ⟨specEtObj B, toSpecSub A B, ⟨⟨t, mem_contSections_of_etale N (specEtObj B) t hteq⟩⟩,
    (counit_lanElt (discSheaf N).obj (specEtObj B) (toSpecSub A B) _).trans
      (ULift.ext _ _ (Subtype.ext (funext ht)))⟩

/-- The zero section over an étale object gives the zero section of the left Kan extension. -/
lemma lanElt_zero {V : (base K).ProEt} (Q : (base K).ProEtᵒᵖ ⥤ ModuleCat.{max (u + 1) r w} Λ)
    (W : (base K).Etale) (h : V ⟶ (etaleInc K).obj W) : lanElt Q W h 0 = 0 := by
  simp [lanElt]

/-- A section over an affine étale object which vanishes on an affine object gives the zero
element of the left Kan extension there. -/
lemma lanElt_eq_zero {V : (base K).ProEt} [IsAffine V.left] (U : (base K).Etale)
    [IsAffine U.left] (k : V ⟶ (etaleInc K).obj U)
    (t : (discSheaf N).obj.obj (op ((etaleInc K).obj U)))
    (ht : ((discSheaf N).obj.map k.op).hom t = 0) : lanElt (discSheaf N).obj U k t = 0 := by
  obtain ⟨B, hB, m, hm⟩ := exists_factor_toSpecSub V U k
  have := etale_of_fg V B hB
  rw [← hm, lanElt_comp]
  have h0 : ((discSheaf N).obj.map ((etaleInc K).map m).op).hom t = 0 := by
    refine ULift.ext _ _ (Subtype.ext (funext fun ψ ↦ ?_))
    obtain ⟨φ, rfl⟩ := GeomPt.map_toSpecSub_surjective (V := V) B ψ
    have := congrArg (fun a : (discSheaf N).obj.obj (op V) ↦ a.down.1 φ) ht
    change t.down.1 (GeomPt.map ((etaleInc K).map m) (GeomPt.map (toSpecSub V B) φ)) = 0
    rwa [← GeomPt.map_comp, hm]
  rw [h0, lanElt_zero]

/-- The sieve of morphisms on which a section of the left Kan extension vanishes is covering as
soon as the section is killed by the counit. -/
lemma vanishing_sieve_mem {U : (base K).ProEt}
    (z : ((etaleInc K).op.lan.obj ((etaleInc K).op ⋙ (discSheaf N).obj)).obj (op U))
    (hz : ((((etaleInc K).op.lanAdjunction _).counit.app (discSheaf N).obj).app (op U)).hom z
      = 0) :
    Sieve.mk (fun V (g : V ⟶ U) ↦ (((etaleInc K).op.lan.obj
        ((etaleInc K).op ⋙ (discSheaf N).obj)).map g.op).hom z = 0)
      (fun {V V'} g hg g' ↦ by
        simp only [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at hg ⊢
        rw [hg, map_zero]) ∈ Scheme.ProEt.topology (base K) U := by
  obtain ⟨W, h, t, rfl⟩ := exists_lanElt (discSheaf N).obj z
  rw [counit_lanElt] at hz
  let G' := etaleInc K
  let R : Sieve U := Sieve.generate fun V g ↦ ∃ (_ : IsAffine V.left)
    (i : W.left.affineCover.I₀) (k : V ⟶ G'.obj (affineCoverEtObj W i)),
      g ≫ h = k ≫ G'.map (affineCoverEtInc W i)
  have hR : R ∈ Scheme.ProEt.topology (base K) U := by
    refine (Scheme.ProEt.topology (base K)).transitive
      ((Scheme.ProEt.topology (base K)).pullback_stable h
        (affineCover_mem_topology (G'.obj W))) R fun V₁ f hf ↦ ?_
    refine (Scheme.ProEt.topology (base K)).superset_covering ?_
      (affineCover_mem_topology V₁)
    rintro V₂ g ⟨V₃, g', g₀, ⟨j⟩, rfl⟩
    obtain ⟨V₄, k₀, i₀, ⟨i⟩, hk⟩ := hf
    have hmem : R (affineCoverInc V₁ j ≫ f) := by
      apply Sieve.le_generate
      refine ⟨inferInstance, i, affineCoverInc V₁ j ≫ k₀, ?_⟩
      change (affineCoverInc V₁ j ≫ f) ≫ h =
        (affineCoverInc V₁ j ≫ k₀) ≫ affineCoverInc (G'.obj W) i
      rw [Category.assoc, Category.assoc, hk]
    exact R.downward_closed hmem g'
  refine (Scheme.ProEt.topology (base K)).superset_covering ?_ hR
  rintro V g ⟨V', g', g₀, ⟨hA, i, k, hk⟩, rfl⟩
  change (((etaleInc K).op.lan.obj ((etaleInc K).op ⋙ (discSheaf N).obj)).map
    (g' ≫ g₀).op).hom (lanElt (discSheaf N).obj W h t) = 0
  rw [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, lanElt_map, hk,
    lanElt_comp, lanElt_eq_zero N (affineCoverEtObj W i) k]
  · exact map_zero _
  · have := congrArg (fun a : (discSheaf N).obj.obj (op U) ↦
      ((discSheaf N).obj.map g₀.op).hom a) hz
    simp only [map_zero] at this
    rw [← this]
    change _ = (((discSheaf N).obj.map h.op ≫ (discSheaf N).obj.map g₀.op).hom t)
    rw [← Functor.map_comp, ← op_comp, hk, op_comp, Functor.map_comp]
    rfl

/-- **The counit of the left Kan extension along the étale inclusion is locally bijective** on
the discrete sheaf of a Galois module, hence becomes invertible after sheafification. -/
theorem W_counit_discSheaf :
    (Scheme.ProEt.topology (base K)).W
      (((etaleInc K).op.lanAdjunction _).counit.app (discSheaf N).obj) := by
  have := proEt_wEqualsLocallyBijective.{u, r, w} (K := K) Λ
  rw [GrothendieckTopology.W_iff_isLocallyBijective]
  refine ⟨⟨fun {X} x y hxy ↦ ?_⟩, ⟨fun {U} s ↦ ?_⟩⟩
  · have hz : ((((etaleInc K).op.lanAdjunction _).counit.app (discSheaf N).obj).app X).hom
        (x - y) = 0 := by
      rwa [map_sub, sub_eq_zero]
    refine (Scheme.ProEt.topology (base K)).superset_covering ?_
      (vanishing_sieve_mem N (U := X.unop) (x - y) hz)
    intro V g hg
    change (((etaleInc K).op.lan.obj ((etaleInc K).op ⋙ (discSheaf N).obj)).map g.op).hom x =
      (((etaleInc K).op.lan.obj ((etaleInc K).op ⋙ (discSheaf N).obj)).map g.op).hom y
    rwa [← sub_eq_zero, ← map_sub]
  · refine (Scheme.ProEt.topology (base K)).superset_covering ?_ (affineCover_mem_topology U)
    rintro V g ⟨V', g', g₀, ⟨i⟩, rfl⟩
    obtain ⟨W, h, x, hx⟩ :=
      exists_lanElt_counit_eq N (((discSheaf N).obj.map (affineCoverInc U i).op).hom s)
    exact (Presheaf.imageSieve _ s).downward_closed ⟨lanElt _ W h x, hx⟩ g'

end Counit

/-! ### The comparison isomorphism -/

variable (K Λ) in
/-- The étale-to-pro-étale direct image `ε_*` on module sheaves. -/
abbrev epsDirect : Sheaf (Scheme.ProEt.topology (base K)) (ModuleCat.{max (u + 1) r w} Λ) ⥤
    Sheaf (base K).smallEtaleTopology (ModuleCat.{max (u + 1) r w} Λ) :=
  (etaleInc K).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r w} Λ)
    (base K).smallEtaleTopology (Scheme.ProEt.topology (base K))

/-- The counit of the left Kan extension along the étale inclusion. -/
def lanCounit (Q : (base K).ProEtᵒᵖ ⥤ ModuleCat.{max (u + 1) r w} Λ) :
    (etaleInc K).op.lan.obj ((etaleInc K).op ⋙ Q) ⟶ Q :=
  ((etaleInc K).op.lanAdjunction _).counit.app Q

/-- Naturality of `lanCounit` in the presheaf. -/
lemma lanCounit_naturality {Q Q' : (base K).ProEtᵒᵖ ⥤ ModuleCat.{max (u + 1) r w} Λ}
    (f : Q ⟶ Q') :
    (etaleInc K).op.lan.map (Functor.whiskerLeft (etaleInc K).op f) ≫ lanCounit Q' =
      lanCounit Q ≫ f :=
  ((etaleInc K).op.lanAdjunction _).counit.naturality f

/-- The isomorphism `ε⁻¹ ε_* 𝒢 ≅ 𝒢` for the discrete sheaf `𝒢` of a Galois module. -/
def inverseImageDirectImageDiscIsoApp (N : Rep.{w} Λ (galoisGroup K)) :
    (Scheme.etaleInverseImage.{u, w, r} (base K) Λ).obj ((epsDirect.{u, r, w} K Λ).obj
      (discSheaf N)) ≅ discSheaf N :=
  @asIso _ _ _ _ ((presheafToSheaf (Scheme.ProEt.topology (base K))
      (ModuleCat.{max (u + 1) r w} Λ)).map (lanCounit (discSheaf N).obj))
      (((Scheme.ProEt.topology (base K)).W_iff _).1 (W_counit_discSheaf N)) ≪≫
    (asIso (sheafificationAdjunction (Scheme.ProEt.topology (base K))
      (ModuleCat.{max (u + 1) r w} Λ)).counit).app (discSheaf N)

/-- Naturality of `inverseImageDirectImageDiscIsoApp` in the Galois module. -/
lemma inverseImageDirectImageDiscIsoApp_naturality {N N' : Rep.{w} Λ (galoisGroup K)}
    (f : N ⟶ N') :
    (Scheme.etaleInverseImage.{u, w, r} (base K) Λ).map ((epsDirect.{u, r, w} K Λ).map
      ((discSheafFunctor Λ).map f)) ≫ (inverseImageDirectImageDiscIsoApp N').hom =
      (inverseImageDirectImageDiscIsoApp N).hom ≫ (discSheafFunctor Λ).map f := by
  let J := Scheme.ProEt.topology (base K)
  let A := ModuleCat.{max (u + 1) r w} Λ
  let F : discSheaf N ⟶ discSheaf N' := (discSheafFunctor Λ).map f
  have h2 : (presheafToSheaf J A).map ((sheafToPresheaf J A).map F) ≫
      (sheafificationAdjunction J A).counit.app (discSheaf N') =
      (sheafificationAdjunction J A).counit.app (discSheaf N) ≫ F :=
    (sheafificationAdjunction J A).counit.naturality F
  change (presheafToSheaf J A).map ((etaleInc K).op.lan.map (Functor.whiskerLeft
      (etaleInc K).op ((sheafToPresheaf J A).map F))) ≫ ((presheafToSheaf J A).map
        (lanCounit (discSheaf N').obj) ≫ (sheafificationAdjunction J A).counit.app
          (discSheaf N')) =
      ((presheafToSheaf J A).map (lanCounit (discSheaf N).obj) ≫
        (sheafificationAdjunction J A).counit.app (discSheaf N)) ≫ F
  rw [← Category.assoc, ← Functor.map_comp, lanCounit_naturality, Functor.map_comp,
    Category.assoc, h2, Category.assoc]
  rfl

variable (Λ) in
/-- Restricting the discrete sheaf to the étale site and pulling back to the pro-étale site
gives the discrete sheaf back, naturally in the Galois module. -/
def inverseImageDirectImageDiscIso :
    discSheafFunctor.{u, r, w} Λ ⋙ epsDirect.{u, r, w} K Λ ⋙
      Scheme.etaleInverseImage.{u, w, r} (base K) Λ ≅ discSheafFunctor.{u, r, w} Λ :=
  NatIso.ofComponents inverseImageDirectImageDiscIsoApp
    (fun f ↦ inverseImageDirectImageDiscIsoApp_naturality f)

variable (Λ) in
/-- The étale sheaf of a Galois module is the restriction of its discrete pro-étale sheaf. -/
def etaleSheafIsoDisc : etaleSheaf K Λ ≅ discSheafFunctor.{u, r, w} Λ ⋙ epsDirect.{u, r, w} K Λ :=
  Functor.isoWhiskerRight (presheafFunctorIsoDisc Λ)
      (presheafToSheaf (base K).smallEtaleTopology (ModuleCat.{max (u + 1) r w} Λ)) ≪≫
    (Iso.refl _ : (discSheafFunctor.{u, r, w} Λ ⋙ sheafToPresheaf (Scheme.ProEt.topology (base K))
        (ModuleCat.{max (u + 1) r w} Λ) ⋙ (Functor.whiskeringLeft _ _ _).obj
          (base K).etaleToProetale.op) ⋙
        presheafToSheaf (base K).smallEtaleTopology (ModuleCat.{max (u + 1) r w} Λ) ≅
      (discSheafFunctor.{u, r, w} Λ ⋙ epsDirect.{u, r, w} K Λ) ⋙
        (sheafToPresheaf (base K).smallEtaleTopology (ModuleCat.{max (u + 1) r w} Λ) ⋙
          presheafToSheaf (base K).smallEtaleTopology (ModuleCat.{max (u + 1) r w} Λ))) ≪≫
    Functor.isoWhiskerLeft (discSheafFunctor.{u, r, w} Λ ⋙ epsDirect.{u, r, w} K Λ)
      (asIso (sheafificationAdjunction (base K).smallEtaleTopology
        (ModuleCat.{max (u + 1) r w} Λ)).counit) ≪≫ Functor.rightUnitor _

variable (Λ) in
/-- **The pro-étale sheaf of a discrete Galois module is the sheaf of locally constant
equivariant functions on geometric points**: `ε⁻¹` of the étale sheaf of `N` is the discrete
sheaf of `N`, naturally in `N`. -/
def proetaleSheafIsoDisc : proetaleSheaf K Λ ≅ discSheafFunctor.{u, r, w} Λ :=
  Functor.isoWhiskerRight (etaleSheafIsoDisc Λ) (Scheme.etaleInverseImage.{u, w, r} (base K) Λ) ≪≫
    Functor.associator _ _ _ ≪≫ inverseImageDirectImageDiscIso Λ

end AlgebraicGeometry.GaloisSheaf
