module

public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.AffineOpenHom
public import StacksFrontier.AlgebraicGeometry.LimitIndexUniverseIntegral.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.Section

/-!
# Eventual finiteness over an affine open of the base, at a free index universe

Let `D` be an inverse system of schemes over a quasi-compact base `S`, indexed by the opposite of
a directed preorder `I` in an arbitrary universe, with finite transition morphisms and structure
morphisms which are affine and locally of finite type. If the morphism from the vertex of a limit
cone of `D` to `S` is integral, then the structure morphism at some sufficiently large stage is
finite.

For an affine open `V` of the base, write `A i = Γ(Dᵢ, pᵢ⁻¹V)` and `L = Γ(lim D, f⁻¹V)`. The
rings `A i` form a directed system with a cocone to `L`, and this cocone is universal among
commutative rings in the universe of the schemes, whatever the universe of the index.

## Main definitions

* `transMap`: the transition map `A i → A j` of the directed system of sections over the
  preimages of an open of the base.
* `limMap`: the cocone `A i → L` induced by a cone of schemes.
* `specCone`: the cone with vertex `Spec C` attached to a compatible family of ring maps
  `A i → C`.

## Main results

* `isSmallColimit_limMap`: for a limit cone, the cocone `limMap` is universal among commutative
  rings in the universe of the schemes.
* `exists_isIntegral_app`: over an affine open of the base the structure morphism is eventually
  integral on sections.
* `exists_isFinite`: the structure morphism is finite at some stage past any given one.

## References

* [The Stacks Project, Tag 09ZN](https://stacks.math.columbia.edu/tag/09ZN)
* [The Stacks Project, Tag 09ZM](https://stacks.math.columbia.edu/tag/09ZM)
-/

@[expose] public section

noncomputable section

universe w u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Stacks.Tag09ZNAffineReduction

open Stacks.AffineAlgebraEquivalence (appLE_congr_hom) in
/-- The restriction map `appLE` of a morphism equal to the identity is the identity. -/
theorem appLE_eq_id {X : Scheme.{u}} (g : X ⟶ X) (hg : g = 𝟙 X) (U : X.Opens)
    (e : U ≤ g ⁻¹ᵁ U) : g.appLE U U e = 𝟙 _ :=
  (appLE_congr_hom hg e (by simp)).trans (Scheme.Hom.appLE_id_eq U)

/-- For a factorization `r = m ≫ q`, the sections of `q` followed by the restriction of `m` are the
sections of `r`. -/
private theorem app_comp_appLE {X Y Z : Scheme.{u}} (m : X ⟶ Y) (q : Y ⟶ Z) (r : X ⟶ Z)
    (hr : r = m ≫ q) (V : Z.Opens) (e : r ⁻¹ᵁ V ≤ m ⁻¹ᵁ (q ⁻¹ᵁ V)) :
    q.app V ≫ m.appLE (q ⁻¹ᵁ V) (r ⁻¹ᵁ V) e = r.app V := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
    Stacks.AffineAlgebraEquivalence.appLE_congr_hom hr.symm _ (le_refl _),
    ← Scheme.Hom.app_eq_appLE]

variable {I : Type w} [Preorder I] {S : Scheme.{u}} (D : Iᵒᵖ ⥤ Scheme.{u})
  (p : ∀ i : I, D.obj (op i) ⟶ S)

/-- Compatibility of the structure morphisms with the transition morphisms. -/
abbrev IsStructureFamily : Prop :=
  ∀ (i j : I) (h : i ≤ j), p j = D.map (homOfLE h).op ≫ p i

variable {D p} (hp : IsStructureFamily D p)

include hp

/-- The preimage of an open of the base at a later stage is the transition-preimage of its
preimage at an earlier stage. -/
theorem preimage_eq (V : S.Opens) {i j : I} (h : i ≤ j) :
    p j ⁻¹ᵁ V = D.map (homOfLE h).op ⁻¹ᵁ (p i ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, ← hp i j h]

/-- The transition map on the sections over the preimage of an open of the base. -/
def transMap (V : S.Opens) (i j : I) (h : i ≤ j) :
    ↥Γ(D.obj (op i), p i ⁻¹ᵁ V) →+* ↥Γ(D.obj (op j), p j ⁻¹ᵁ V) :=
  ((D.map (homOfLE h).op).appLE (p i ⁻¹ᵁ V) (p j ⁻¹ᵁ V) (preimage_eq hp V h).le).hom

/-- `transMap` is the restriction map along the transition morphism. -/
theorem transMap_apply (V : S.Opens) (i j : I) (h : i ≤ j)
    (x : ↥Γ(D.obj (op i), p i ⁻¹ᵁ V)) :
    transMap hp V i j h x =
      ((D.map (homOfLE h).op).appLE (p i ⁻¹ᵁ V) (p j ⁻¹ᵁ V) (preimage_eq hp V h).le).hom x :=
  rfl

/-- The transition map from a stage to itself is the identity. -/
theorem transMap_self (V : S.Opens) (i : I) (x : ↥Γ(D.obj (op i), p i ⁻¹ᵁ V)) :
    transMap hp V i i le_rfl x = x := by
  rw [transMap_apply, appLE_eq_id _ (by
    rw [show (homOfLE (le_refl i)).op = 𝟙 (op i) from Subsingleton.elim _ _]; exact D.map_id _)]
  simp

/-- The transition maps compose: the map from `i` to `k` is the map from `j` to `k` after the
map from `i` to `j`. -/
theorem transMap_trans (V : S.Opens) {i j k : I} (hij : i ≤ j) (hjk : j ≤ k)
    (x : ↥Γ(D.obj (op i), p i ⁻¹ᵁ V)) :
    transMap hp V j k hjk (transMap hp V i j hij x) = transMap hp V i k (hij.trans hjk) x := by
  simp only [transMap_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, ← D.map_comp,
    show (homOfLE hjk).op ≫ (homOfLE hij).op = (homOfLE (hij.trans hjk)).op from
      Subsingleton.elim _ _]

/-- The sections over the preimages of an open of the base form a directed system under the
transition maps `transMap`. -/
instance directedSystem_transMap (V : S.Opens) :
    DirectedSystem (fun i : I ↦ ↥Γ(D.obj (op i), p i ⁻¹ᵁ V))
      fun i j h ↦ transMap hp V i j h :=
  { map_self := fun ⦃i⦄ x ↦ transMap_self hp V i x
    map_map := fun ⦃_ _ _⦄ hij hjk x ↦ transMap_trans hp V hij hjk x }

variable {c : Cone D} {f : c.pt ⟶ S}

omit hp in
/-- The preimage of an open of the base in the vertex of a cone is the pullback along the
projection of its preimage at any stage. -/
theorem limPreimage_eq (hf : ∀ i : I, f = c.π.app (op i) ≫ p i) (V : S.Opens) (i : I) :
    f ⁻¹ᵁ V = c.π.app (op i) ⁻¹ᵁ (p i ⁻¹ᵁ V) := by
  rw [hf i, Scheme.Hom.comp_preimage]

/-- The cocone on the systems of sections over the preimages of `V` induced by a cone of
schemes. -/
def limMap (hf : ∀ i : I, f = c.π.app (op i) ≫ p i) (V : S.Opens) (i : I) :
    ↥Γ(D.obj (op i), p i ⁻¹ᵁ V) →+* ↥Γ(c.pt, f ⁻¹ᵁ V) :=
  ((c.π.app (op i)).appLE (p i ⁻¹ᵁ V) (f ⁻¹ᵁ V) (limPreimage_eq hf V i).le).hom

/-- The cocone is compatible with the transition maps, as an identity of restriction maps. -/
theorem limMap_comp_transMap (hf : ∀ i : I, f = c.π.app (op i) ≫ p i) (V : S.Opens) (i j : I)
    (h : i ≤ j) :
    ((D.map (homOfLE h).op).appLE (p i ⁻¹ᵁ V) (p j ⁻¹ᵁ V) (preimage_eq hp V h).le)
        ≫ ((c.π.app (op j)).appLE (p j ⁻¹ᵁ V) (f ⁻¹ᵁ V) (limPreimage_eq hf V j).le)
      = (c.π.app (op i)).appLE (p i ⁻¹ᵁ V) (f ⁻¹ᵁ V) (limPreimage_eq hf V i).le := by
  rw [Scheme.Hom.appLE_comp_appLE]
  exact Stacks.AffineAlgebraEquivalence.appLE_congr_hom (c.w (homOfLE h).op) _ _

/-- The cocone `limMap` is compatible with the transition maps `transMap`. -/
theorem limMap_transMap (hf : ∀ i : I, f = c.π.app (op i) ≫ p i) (V : S.Opens) (i j : I)
    (h : i ≤ j) (x : ↥Γ(D.obj (op i), p i ⁻¹ᵁ V)) :
    limMap hf V j (transMap hp V i j h x) = limMap hf V i x := by
  simpa [limMap, transMap] using
    congrArg (fun φ : Γ(D.obj (op i), p i ⁻¹ᵁ V) ⟶ Γ(c.pt, f ⁻¹ᵁ V) ↦ φ.hom x)
      (limMap_comp_transMap hp hf V i j h)

/-- The cone with vertex `Spec C` determined by a compatible family of ring maps out of the
sections over the preimages of an affine open `V` of the base, when those preimages are affine.
-/
def specCone (V : S.Opens) (haff : ∀ i : I, IsAffineOpen (p i ⁻¹ᵁ V))
    (C : Type u) [CommRing C] (g : ∀ i : I, ↥Γ(D.obj (op i), p i ⁻¹ᵁ V) →+* C)
    (hg : ∀ (i j : I) (h : i ≤ j) (x : ↥Γ(D.obj (op i), p i ⁻¹ᵁ V)),
      g j (transMap hp V i j h x) = g i x) :
    Cone D where
  pt := Spec (CommRingCat.of C)
  π :=
  { app := fun X ↦ Spec.map (CommRingCat.ofHom (g X.unop)) ≫ (haff X.unop).fromSpec
    naturality := fun X Y φ ↦ by
      have h : Y.unop ≤ X.unop := leOfHom φ.unop
      have hφ : (homOfLE h).op = φ := Subsingleton.elim _ _
      have hkey : (D.map (homOfLE h).op).appLE (p Y.unop ⁻¹ᵁ V) (p X.unop ⁻¹ᵁ V)
            (preimage_eq hp V h).le ≫ CommRingCat.ofHom (g X.unop)
          = CommRingCat.ofHom (g Y.unop) :=
        CommRingCat.hom_ext (RingHom.ext fun x ↦ by
          simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
          exact hg Y.unop X.unop h x)
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
      rw [Category.assoc, ← hφ, ← IsAffineOpen.SpecMap_appLE_fromSpec
        (D.map (homOfLE h).op) (haff Y.unop) (haff X.unop) (preimage_eq hp V h).le,
        ← Spec.map_comp_assoc, hkey] }

/-- The projection of `specCone` at a stage is `Spec` of the ring map at that stage followed by
the inclusion of the affine preimage of `V`. -/
@[simp] theorem specCone_π_app (V : S.Opens) (haff : ∀ i : I, IsAffineOpen (p i ⁻¹ᵁ V))
    (C : Type u) [CommRing C] (g : ∀ i : I, ↥Γ(D.obj (op i), p i ⁻¹ᵁ V) →+* C)
    (hg : ∀ (i j : I) (h : i ≤ j) (x : ↥Γ(D.obj (op i), p i ⁻¹ᵁ V)),
      g j (transMap hp V i j h x) = g i x) (X : Iᵒᵖ) :
    (specCone hp V haff C g hg).π.app X
      = Spec.map (CommRingCat.ofHom (g X.unop)) ≫ (haff X.unop).fromSpec := rfl

/-- If `c` is a limit cone of the system and `V` is an open of the base whose preimage at every
stage is affine and whose preimage in the vertex is affine, then the cocone of sections over those
preimages is universal among commutative rings in the schemes' own universe. -/
theorem isSmallColimit_limMap [Nonempty I] (hc : IsLimit c)
    (hf : ∀ i : I, f = c.π.app (op i) ≫ p i) (V : S.Opens)
    (haff : ∀ i : I, IsAffineOpen (p i ⁻¹ᵁ V)) (hW : IsAffineOpen (f ⁻¹ᵁ V)) :
    Stacks.IntegralLimitAlgebra.IsSmallColimit (fun i j h ↦ transMap hp V i j h)
      (limMap hf V) := by
  intro C _ g hg
  obtain ⟨i₀⟩ := ‹Nonempty I›
  obtain ⟨m, hm⟩ : ∃ m : Spec (CommRingCat.of C) ⟶ c.pt,
      ∀ X, m ≫ c.π.app X = (specCone hp V haff C g hg).π.app X :=
    ⟨hc.lift (specCone hp V haff C g hg), fun X ↦ hc.fac _ X⟩
  have hrange : Set.range m ⊆ Set.range hW.fromSpec := by
    rw [hW.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    have h1 : (m ≫ c.π.app (op i₀)).base x ∈ (p i₀ ⁻¹ᵁ V : (D.obj (op i₀)).Opens) := by
      rw [hm (op i₀), specCone_π_app]
      have : ((Spec.map (CommRingCat.ofHom (g i₀)) ≫ (haff i₀).fromSpec)).base x
          ∈ Set.range (haff i₀).fromSpec := ⟨_, rfl⟩
      rwa [(haff i₀).range_fromSpec] at this
    change m.base x ∈ ((f ⁻¹ᵁ V : c.pt.Opens) : Set c.pt)
    rwa [limPreimage_eq hf V i₀]
  refine ⟨(Spec.preimage (IsOpenImmersion.lift hW.fromSpec m hrange)).hom, fun i x ↦ ?_⟩
  have hl : IsOpenImmersion.lift hW.fromSpec m hrange ≫ hW.fromSpec = m :=
    IsOpenImmersion.lift_fac _ _ _
  have hkey : ((c.π.app (op i)).appLE (p i ⁻¹ᵁ V) (f ⁻¹ᵁ V) (limPreimage_eq hf V i).le)
        ≫ Spec.preimage (IsOpenImmersion.lift hW.fromSpec m hrange)
      = CommRingCat.ofHom (g i) := by
    refine Spec.map_injective ?_
    rw [Spec.map_comp, Spec.map_preimage]
    refine (cancel_mono (haff i).fromSpec).mp ?_
    rw [Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec (c.π.app (op i)) (haff i) hW
      (limPreimage_eq hf V i).le, ← Category.assoc, hl, hm (op i), specCone_π_app]
  simpa [limMap] using
    congrArg (fun φ : Γ(D.obj (op i), p i ⁻¹ᵁ V) ⟶ CommRingCat.of C ↦ φ.hom x) hkey

omit hp in
/-- The restriction map of a finite morphism over an affine open is module-finite, in the
`appLE` form, for a source open which is *equal* to the preimage. -/
theorem finite_appLE {X Y : Scheme.{u}} (g : X ⟶ Y) [IsFinite g] {U : Y.Opens}
    (hU : IsAffineOpen U) {W : X.Opens} (hW : W = g ⁻¹ᵁ U) (e : W ≤ g ⁻¹ᵁ U) :
    ((g.appLE U W e).hom).Finite := by
  subst hW
  rw [show g.appLE U (g ⁻¹ᵁ U) e = g.app U from (Scheme.Hom.app_eq_appLE g).symm]
  exact IsFinite.finite_app g U hU

/-- The structure morphisms are compatible with the transition maps on sections, as an identity
of restriction maps. -/
theorem app_comp_transMap (V : S.Opens) (i j : I) (h : i ≤ j) :
    ((p i).app V) ≫ ((D.map (homOfLE h).op).appLE (p i ⁻¹ᵁ V) (p j ⁻¹ᵁ V) (preimage_eq hp V h).le)
      = (p j).app V :=
  app_comp_appLE _ _ _ (hp i j h) V _

/-- The structure morphisms are compatible with the transition maps on sections. -/
private theorem transMap_comp_app (V : S.Opens) (i j : I) (h : i ≤ j) :
    (transMap hp V i j h).comp ((p i).app V).hom = ((p j).app V).hom :=
  RingHom.ext fun x ↦ by
    simpa [transMap] using ConcreteCategory.congr_hom (app_comp_transMap hp V i j h) x

omit hp in
/-- The structure morphism out of the vertex factors the cocone through the structure morphism at
any stage, as an identity of restriction maps. -/
theorem app_comp_limMap (hf : ∀ i : I, f = c.π.app (op i) ≫ p i) (V : S.Opens) (i : I) :
    ((p i).app V) ≫ ((c.π.app (op i)).appLE (p i ⁻¹ᵁ V) (f ⁻¹ᵁ V) (limPreimage_eq hf V i).le)
      = f.app V :=
  app_comp_appLE _ _ _ (hf i) V _

/-- The transition map on sections over the preimage of an affine open of the base is
module-finite when the transition morphisms are finite and the structure morphisms affine. -/
theorem finite_transMap (haff : ∀ i : I, IsAffineHom (p i))
    (hfinite : ∀ (i j : I) (h : i ≤ j), IsFinite (D.map (homOfLE h).op))
    (V : S.Opens) (hV : IsAffineOpen V) (i j : I) (h : i ≤ j) :
    (transMap hp V i j h).Finite := by
  have := hfinite i j h
  have := haff i
  exact finite_appLE _ (hV.preimage (p i)) (preimage_eq hp V h) _

/-- Let `D` be an inverse system of schemes over `S` with finite transition morphisms and
structure morphisms which are affine and locally of finite type, indexed by a nonempty directed
preorder in an arbitrary universe. If the morphism from the vertex of a limit cone to `S` is
integral, then for every affine open `V` of `S` and every index `i₀` there is `j ≥ i₀` such that
the ring map `Γ(S, V) → Γ(Dⱼ, pⱼ⁻¹V)` is integral. -/
theorem exists_isIntegral_app [IsDirectedOrder I] [Nonempty I]
    (haffHom : ∀ i : I, IsAffineHom (p i))
    (hc : IsLimit c) (hf : ∀ i : I, f = c.π.app (op i) ≫ p i) (hfint : IsIntegralHom f)
    (hfinite : ∀ (i j : I) (h : i ≤ j), IsFinite (D.map (homOfLE h).op))
    (hlft : ∀ i : I, LocallyOfFiniteType (p i))
    (V : S.Opens) (hV : IsAffineOpen V) (i₀ : I) :
    ∃ (j : I) (_ : i₀ ≤ j), RingHom.IsIntegral (((p j).app V).hom) := by
  have hah := haffHom
  have haff : ∀ i : I, IsAffineOpen (p i ⁻¹ᵁ V) := fun i ↦ have := hah i; hV.preimage (p i)
  have hW : IsAffineOpen (f ⁻¹ᵁ V) := have := hfint; hV.preimage f
  have hfin : ∀ (i j : I) (h : i ≤ j), (transMap hp V i j h).Finite :=
    fun i j h ↦ finite_transMap hp haffHom hfinite V hV i j h
  have hr : ∀ (i j : I) (h : i ≤ j) (x : ↥Γ(S, V)),
      transMap hp V i j h (((p i).app V).hom x) = ((p j).app V).hom x :=
    fun i j h x ↦ RingHom.congr_fun (transMap_comp_app hp V i j h) x
  have hint : ((limMap hf V i₀).comp (((p i₀).app V).hom)).IsIntegral := by
    have heq : (limMap hf V i₀).comp (((p i₀).app V).hom) = (f.app V).hom := by
      refine RingHom.ext fun x ↦ ?_
      simpa [limMap] using ConcreteCategory.congr_hom (app_comp_limMap hf V i₀) x
    rw [heq]
    have := hfint
    exact IsIntegralHom.isIntegral_app f V hV
  have hft : (((p i₀).app V).hom).FiniteType := by
    have h := HasRingHomProperty.appLE @LocallyOfFiniteType (p i₀) (hlft i₀) ⟨V, hV⟩
      ⟨p i₀ ⁻¹ᵁ V, haff i₀⟩ le_rfl
    rwa [← Scheme.Hom.app_eq_appLE] at h
  exact Stacks.IntegralLimitAlgebra.exists_isIntegral (fun i j h ↦ transMap hp V i j h)
    hfin (fun i ↦ ((p i).app V).hom) hr (limMap_transMap hp hf V)
    (isSmallColimit_limMap hp hc hf V haff hW) i₀ hft hint

/-- Let `D` be an inverse system of schemes indexed by the opposite of a nonempty directed preorder
`I` in an arbitrary universe, over a quasi-compact base `S`, with finite transition morphisms and
structure morphisms which are affine and locally of finite type.  If the morphism from the vertex
of a limit cone to `S` is integral, then the structure morphism at some stage past any prescribed
one is finite. -/
theorem exists_isFinite [IsDirectedOrder I] [Nonempty I] [CompactSpace S]
    (haffHom : ∀ i : I, IsAffineHom (p i)) (hc : IsLimit c)
    (hf : ∀ i : I, f = c.π.app (op i) ≫ p i) (hfint : IsIntegralHom f)
    (hfinite : ∀ (i j : I) (h : i ≤ j), IsFinite (D.map (homOfLE h).op))
    (hlft : ∀ i : I, LocallyOfFiniteType (p i)) (i₀ : I) :
    ∃ (j : I) (_ : i₀ ≤ j), IsFinite (p j) := by
  classical
  obtain ⟨σ, hσ⟩ := isCompact_univ.elim_finite_subcover
    (fun U : S.affineOpens ↦ ((U : S.Opens) : Set S)) (fun U ↦ (U : S.Opens).2) (by
      intro x _
      have h : x ∈ (⨆ U : S.affineOpens, (U : S.Opens)) := by
        rw [iSup_affineOpens_eq_top S]; trivial
      simpa using h)
  have key : ∀ U : S.affineOpens, ∃ (j : I) (_ : i₀ ≤ j),
      RingHom.IsIntegral (((p j).app (U : S.Opens)).hom) :=
    fun U ↦ exists_isIntegral_app hp haffHom hc hf hfint hfinite hlft (U : S.Opens) U.2 i₀
  choose jU hjU hjUint using key
  obtain ⟨k, hk⟩ := (insert i₀ (σ.image jU)).exists_le
  refine ⟨k, hk i₀ (Finset.mem_insert_self _ _), ?_⟩
  refine (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr ⟨?_, hlft k⟩
  refine isIntegralHom_of_iSup_eq_top _ (fun U : {U // U ∈ σ} ↦ ((U.1 : S.Opens))) ?_ ?_
  · refine TopologicalSpace.Opens.ext ?_
    rw [TopologicalSpace.Opens.coe_iSup]
    refine Set.eq_univ_of_univ_subset (hσ.trans ?_)
    simp only [Set.iUnion_subset_iff]
    intro U hU
    exact Set.subset_iUnion_of_subset ⟨U, hU⟩ le_rfl
  · intro U
    have hkU : jU U.1 ≤ k := hk _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ U.2))
    change IsIntegralHom (p k ∣_ ((U.1 : S.Opens)))
    have : IsAffine ((U.1 : S.Opens)).toScheme := U.1.2
    have hA : IsAffineOpen (p k ⁻¹ᵁ ((U.1 : S.Opens))) :=
      have := haffHom k; U.1.2.preimage (p k)
    have hI : RingHom.IsIntegral (((p k).app ((U.1 : S.Opens))).hom) := by
      have heq : ((p k).app (U.1 : S.Opens)).hom
          = (transMap hp (U.1 : S.Opens) (jU U.1) k hkU).comp
            (((p (jU U.1)).app (U.1 : S.Opens)).hom) := by
        exact (transMap_comp_app hp (U.1 : S.Opens) (jU U.1) k hkU).symm
      rw [heq]
      exact RingHom.isIntegral_stableUnderComposition _ _ (hjUint U.1)
        (finite_transMap hp haffHom hfinite _ U.1.2 _ _ hkU).to_isIntegral
    exact isIntegralHom_of_isAffine _ hA (isIntegral_app_top_morphismRestrict _ _ hI)

end Stacks.Tag09ZNAffineReduction

end

end
