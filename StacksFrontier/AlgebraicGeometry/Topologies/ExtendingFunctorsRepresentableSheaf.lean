module

public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsLimits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Representable functors and fibre products against the conditions of Stacks 0EUW

Two conditions on a functor on `Sch/S` enter Stacks 0EUW: being a Zariski sheaf, and taking
directed inverse limits of affine schemes over `S` to filtered colimits. This file records which
functors satisfy them.

* The functor of points of an object of `Sch/S` is always a Zariski sheaf, and it takes directed
  inverse limits of affines to filtered colimits when the object is locally of finite
  presentation over `S` (Stacks 01ZC).
* Both conditions pass to the upper left corner of a Cartesian square of functors.

## Main definitions

* `AlgebraicGeometry.ExtendingFunctors.opensCover`: the open cover of a scheme by a family of
  opens covering it.

## Main results

* `AlgebraicGeometry.ExtendingFunctors.existsUnique_glue_opens`: morphisms of schemes glue over an
  open cover.
* `AlgebraicGeometry.ExtendingFunctors.isZariskiSheaf_uliftYoneda`: the functor of points of an
  object of `Sch/S` is a Zariski sheaf.
* `AlgebraicGeometry.ExtendingFunctors.preservesAffineLimits_uliftYoneda`: the functor of points
  of an object locally of finite presentation over `S` takes directed inverse limits of affine
  schemes over `S` to filtered colimits.
* `AlgebraicGeometry.ExtendingFunctors.isZariskiSheaf_of_isPullback` and
  `AlgebraicGeometry.ExtendingFunctors.preservesAffineLimits_of_isPullback`: both conditions pass
  to a fibre product of functors.

## References

* [Stacks Project, Tag 0EUW](https://stacks.math.columbia.edu/tag/0EUW)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ExtendingFunctors

universe w u

variable {S : Scheme.{u}}

/-! ### Gluing morphisms of schemes over an open cover -/

/-- The open cover of a scheme by a family of opens whose supremum is everything. -/
@[implicit_reducible]
def opensCover {X : Scheme.{u}} {J : Type u} (V : J → X.Opens) (hV : ⨆ i, V i = ⊤) :
    X.OpenCover where
  I₀ := J
  X i := (V i).toScheme
  f i := (V i).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    have hx : x ∈ ⨆ i, V i := by rw [hV]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨i, ⟨⟨x, hi⟩, rfl⟩⟩

/-- The morphisms of `opensCover V hV` are the inclusions of the opens `V i`. -/
@[simp]
lemma opensCover_f {X : Scheme.{u}} {J : Type u} (V : J → X.Opens) (hV : ⨆ i, V i = ⊤) (i : J) :
    (opensCover V hV).f i = (V i).ι := rfl

/-- **Morphisms of schemes glue over an open cover.** A family of morphisms out of the members of
an open cover of `X` which agree on the pairwise intersections is the restriction of a unique
morphism out of `X`. -/
theorem existsUnique_glue_opens {X Y : Scheme.{u}} {J : Type u} (V : J → X.Opens)
    (hV : ⨆ i, V i = ⊤) (h : ∀ i, (V i).toScheme ⟶ Y)
    (hcompat : ∀ i j, X.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ h i
      = X.homOfLE (inf_le_right : V i ⊓ V j ≤ V j) ≫ h j) :
    ∃! g : X ⟶ Y, ∀ i, (V i).ι ≫ g = h i := by
  refine ⟨(opensCover V hV).glueMorphisms h ?_,
    fun i => (opensCover V hV).ι_glueMorphisms h _ i, fun g hg => ?_⟩
  · intro i j
    change pullback.fst (V i).ι (V j).ι ≫ h i = pullback.snd (V i).ι (V j).ι ≫ h j
    rw [← cancel_epi (isPullback_opens_inf (V i) (V j)).isoPullback.hom, ← Category.assoc,
      ← Category.assoc, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_hom_snd]
    exact hcompat i j
  · refine (opensCover V hV).hom_ext _ _ fun i => ?_
    change (V i).ι ≫ g = (V i).ι ≫ _
    rw [hg i]
    exact ((opensCover V hV).ι_glueMorphisms h _ i).symm

/-! ### The functor of points -/

/-- **The functor of points of an object of `Sch/S` is a Zariski sheaf.** -/
theorem isZariskiSheaf_uliftYoneda (X : Over S) :
    IsZariskiSheaf (uliftYoneda.{max w (u + 1)}.obj X) := by
  intro Z ι V hcov s hs
  have hsleft : ∀ i j, Z.left.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ (s i).down.left
      = Z.left.homOfLE (inf_le_right : V i ⊓ V j ≤ V j) ≫ (s j).down.left := by
    intro i j
    simpa using congrArg (fun t : ULift.{max w (u + 1)} (overOpen Z (V i ⊓ V j) ⟶ X) =>
      t.down.left) (hs i j)
  obtain ⟨g, hg, hgu⟩ :=
    existsUnique_glue_opens V hcov (fun i => (s i).down.left) hsleft
  have hgS : g ≫ X.hom = Z.hom := by
    refine (opensCover V hcov).hom_ext _ _ fun i => ?_
    change (V i).ι ≫ g ≫ X.hom = (V i).ι ≫ Z.hom
    rw [← Category.assoc, hg i]
    simp
  refine ⟨ULift.up (Over.homMk g hgS), fun i => ?_, fun t ht => ?_⟩
  · refine congrArg ULift.up (Over.OverMorphism.ext ?_)
    change (overOpenι Z (V i)).left ≫ g = (s i).down.left
    rw [overOpenι_left, hg i]
  · have hprop : ∀ i, (V i).ι ≫ t.down.left = (s i).down.left := by
      intro i
      simpa using congrArg (fun r : ULift.{max w (u + 1)} (overOpen Z (V i) ⟶ X) =>
        r.down.left) (ht i)
    exact congrArg ULift.up (Over.OverMorphism.ext (hgu _ hprop))

/-- **The functor of points of an object locally of finite presentation over `S` takes directed
inverse limits of affine schemes over `S` to filtered colimits.** This is the implication
(1) ⇒ (2) of Stacks 01ZC. -/
@[ega "IV 17.3.2" "Forward implication", sga "3 XI 3.2" "partial"]
theorem preservesAffineLimits_uliftYoneda (X : Over S) [LocallyOfFinitePresentation X.hom] :
    PreservesAffineLimits (uliftYoneda.{max w (u + 1)}.obj X) := by
  intro Λ _ _ _ D hD c hc
  obtain ⟨hcol⟩ :=
    (Scheme.isLimitPreserving_yoneda_of_locallyOfFinitePresentation X Λᵒᵖ D hD).preserves hc.op
  exact ⟨isColimitOfPreserves uliftFunctor.{max w (u + 1)} hcol⟩

/-! ### Fibre products -/

section GeneralPullback

universe v v₁ u₁ v₂ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {A B K E : 𝒞ᵒᵖ ⥤ Type v}
  {p : A ⟶ B} {q : A ⟶ K} {f : B ⟶ E} {g : K ⟶ E}

/-- A Cartesian square of functors is Cartesian at every object. -/
theorem isPullback_app (h : IsPullback p q f g) (Z : 𝒞ᵒᵖ) :
    IsPullback (p.app Z) (q.app Z) (f.app Z) (g.app Z) :=
  h.map ((evaluation 𝒞ᵒᵖ (Type v)).obj Z)

/-- Two sections of the upper left corner of a Cartesian square of functors with the same two
projections are equal. -/
theorem eq_of_isPullback_app (h : IsPullback p q f g) {Z : 𝒞ᵒᵖ} {a a' : A.obj Z}
    (h₁ : p.app Z a = p.app Z a') (h₂ : q.app Z a = q.app Z a') : a = a' :=
  Types.ext_of_isPullback (isPullback_app h Z) h₁ h₂

/-- A compatible pair of sections of the two other corners of a Cartesian square of functors comes
from a section of the upper left corner. -/
theorem exists_of_isPullback_app (h : IsPullback p q f g) {Z : 𝒞ᵒᵖ} (b : B.obj Z)
    (c : K.obj Z) (hbc : f.app Z b = g.app Z c) :
    ∃ a : A.obj Z, p.app Z a = b ∧ q.app Z a = c :=
  Types.exists_of_isPullback (isPullback_app h Z) b c hbc

/-- The two ways round a Cartesian square of functors agree on sections. -/
theorem app_apply_comm (h : IsPullback p q f g) (Z : 𝒞ᵒᵖ) (a : A.obj Z) :
    f.app Z (p.app Z a) = g.app Z (q.app Z a) :=
  types_congr_hom (NatTrans.congr_app h.w Z) a

/-- If `A ≅ B` and `A` carries the opposite of a cone `c` to a colimit cocone, so does `B`. -/
def isColimit_mapCocone_of_natIso {A B : 𝒞ᵒᵖ ⥤ Type v} (e : A ≅ B) {J : Type u₂}
    [Category.{v₂} J] {D : J ⥤ 𝒞} (c : Cone D) (h : IsColimit (A.mapCocone c.op)) :
    IsColimit (B.mapCocone c.op) :=
  IsColimit.precomposeHomEquiv (Functor.isoWhiskerLeft D.op e) (B.mapCocone c.op)
    (h.ofIsoColimit (Cocones.ext (e.app (op c.pt)) fun _ => e.hom.naturality _))

variable {Λ : Type u} [PartialOrder Λ] (D : Λᵒᵖ ⥤ 𝒞)

/-- Restriction to a stage of an inverse system factors through the intermediate stages. -/
private theorem map_op_trans (G : 𝒞ᵒᵖ ⥤ Type v)
    {l m n : Λ} (hlm : l ≤ m) (hmn : m ≤ n) (y : G.obj (op (D.obj (op l)))) :
    G.map (D.map (homOfLE (hlm.trans hmn)).op).op y
      = G.map (D.map (homOfLE hmn).op).op (G.map (D.map (homOfLE hlm).op).op y) := by
  have he : (homOfLE (hlm.trans hmn) : l ⟶ n).op
      = ((homOfLE hmn : m ⟶ n).op ≫ (homOfLE hlm : l ⟶ m).op) := Subsingleton.elim _ _
  rw [he, D.map_comp, op_comp, Functor.map_comp]
  rfl

variable [Nonempty Λ] [IsDirectedOrder Λ]

/-- **A filtered colimit of sets commutes with a fibre product.** If each of the other three
corners of a Cartesian square of functors carries the opposite of a cone `c` over a directed
inverse system to a colimit cocone, then so does the upper left corner. -/
theorem nonempty_isColimit_mapCocone_of_isPullback (h : IsPullback p q f g) (c : Cone D)
    (hcolB : IsColimit (B.mapCocone c.op)) (hcolK : IsColimit (K.mapCocone c.op))
    (hcolE : IsColimit (E.mapCocone c.op)) : Nonempty (IsColimit (A.mapCocone c.op)) := by
  have hπ : ∀ (G : 𝒞ᵒᵖ ⥤ Type v) {l m : Λ} (hlm : l ≤ m)
      (y : G.obj (op (D.obj (op l)))),
      G.map (c.π.app (op m)).op (G.map (D.map (homOfLE hlm).op).op y)
        = G.map (c.π.app (op l)).op y := by
    intro G l m hlm y
    rw [← Functor.map_comp_apply, ← op_comp, c.w (homOfLE hlm).op]
  refine nonempty_isColimit_op_of_exists A D c (fun x => ?_) (fun l a a' haa' => ?_)
  · obtain ⟨l₁, y₁, hy₁⟩ := exists_map_eq_of_isColimit_op B D c hcolB (p.app _ x)
    obtain ⟨l₂, y₂, hy₂⟩ := exists_map_eq_of_isColimit_op K D c hcolK (q.app _ x)
    obtain ⟨m, hm₁, hm₂⟩ := exists_ge_ge l₁ l₂
    obtain ⟨z₁, hz₁⟩ : ∃ z, z = B.map (D.map (homOfLE hm₁).op).op y₁ := ⟨_, rfl⟩
    obtain ⟨z₂, hz₂⟩ : ∃ z, z = K.map (D.map (homOfLE hm₂).op).op y₂ := ⟨_, rfl⟩
    have hz₁' : B.map (c.π.app (op m)).op z₁ = p.app _ x := by rw [hz₁, hπ B hm₁ y₁, hy₁]
    have hz₂' : K.map (c.π.app (op m)).op z₂ = q.app _ x := by rw [hz₂, hπ K hm₂ y₂, hy₂]
    have hmid : E.map (c.π.app (op m)).op (f.app _ z₁)
        = E.map (c.π.app (op m)).op (g.app _ z₂) := by
      rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, hz₁', hz₂']
      exact app_apply_comm h _ x
    obtain ⟨n, hn, hneq⟩ :=
      exists_le_map_eq_of_isColimit_op E D c hcolE (f.app _ z₁) (g.app _ z₂) hmid
    have hcompat : f.app (op (D.obj (op n))) (B.map (D.map (homOfLE hn).op).op z₁)
        = g.app (op (D.obj (op n))) (K.map (D.map (homOfLE hn).op).op z₂) := by
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
      exact hneq
    obtain ⟨a, ha₁, ha₂⟩ := exists_of_isPullback_app h _ _ hcompat
    refine ⟨n, a, eq_of_isPullback_app h ?_ ?_⟩
    · rw [NatTrans.naturality_apply, ha₁, hπ B hn z₁, hz₁']
      rfl
    · rw [NatTrans.naturality_apply, ha₂, hπ K hn z₂, hz₂']
      rfl
  · have hcongr : ∀ {G : 𝒞ᵒᵖ ⥤ Type v} (φ : A ⟶ G),
        G.map (c.π.app (op l)).op (φ.app _ a) = G.map (c.π.app (op l)).op (φ.app _ a') := by
      intro G φ
      rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, haa']
    obtain ⟨m₁, hm₁, he₁⟩ := exists_le_map_eq_of_isColimit_op B D c hcolB _ _ (hcongr p)
    obtain ⟨m₂, hm₂, he₂⟩ := exists_le_map_eq_of_isColimit_op K D c hcolK _ _ (hcongr q)
    obtain ⟨n, hn₁, hn₂⟩ := exists_ge_ge m₁ m₂
    refine ⟨n, hm₁.trans hn₁, eq_of_isPullback_app h ?_ ?_⟩ <;>
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
    · rw [map_op_trans D B hm₁ hn₁, map_op_trans D B hm₁ hn₁, he₁]
    · rw [map_op_trans D K hm₂ hn₂, map_op_trans D K hm₂ hn₂, he₂]

end GeneralPullback

section OverPullback

variable {A B K E : (Over S)ᵒᵖ ⥤ Type (max w (u + 1))}
  {p : A ⟶ B} {q : A ⟶ K} {f : B ⟶ E} {g : K ⟶ E}

/-- **The Zariski sheaf condition passes to a fibre product of functors.** -/
theorem isZariskiSheaf_of_isPullback (h : IsPullback p q f g) (haB : IsZariskiSheaf B)
    (haK : IsZariskiSheaf K) (haE : IsZariskiSheaf E) : IsZariskiSheaf A := by
  intro X ι V hcov s hs
  obtain ⟨b, hb, hbu⟩ := haB X ι V hcov (fun i => p.app _ (s i)) (by
    intro i j
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, hs i j])
  obtain ⟨c, hc, hcu⟩ := haK X ι V hcov (fun i => q.app _ (s i)) (by
    intro i j
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, hs i j])
  have hfg : f.app (op X) b = g.app (op X) c := by
    refine zariskiSheaf_ext haE V hcov _ _ fun i => ?_
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, hb i, hc i]
    exact app_apply_comm h _ (s i)
  obtain ⟨t, ht₁, ht₂⟩ := exists_of_isPullback_app h b c hfg
  refine ⟨t, fun i => ?_, fun t' ht' => ?_⟩
  · refine eq_of_isPullback_app h ?_ ?_
    · rw [NatTrans.naturality_apply, ht₁, hb i]
    · rw [NatTrans.naturality_apply, ht₂, hc i]
  · refine eq_of_isPullback_app h ?_ ?_
    · rw [ht₁]
      refine hbu _ fun i => ?_
      rw [← NatTrans.naturality_apply, ht' i]
    · rw [ht₂]
      refine hcu _ fun i => ?_
      rw [← NatTrans.naturality_apply, ht' i]

/-- **The limit condition of Stacks 0EUW passes to a fibre product of functors.** -/
theorem preservesAffineLimits_of_isPullback (h : IsPullback p q f g)
    (hbB : PreservesAffineLimits B) (hbK : PreservesAffineLimits K)
    (hbE : PreservesAffineLimits E) : PreservesAffineLimits A := fun Λ _ _ _ D hD c hc =>
  nonempty_isColimit_mapCocone_of_isPullback D h c (hbB Λ D hD c hc).some
    (hbK Λ D hD c hc).some (hbE Λ D hD c hc).some

end OverPullback

section SubcategoryPullback

variable {P : ObjectProperty (Over S)}
  {A B K E : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1))}
  {p : A ⟶ B} {q : A ⟶ K} {f : B ⟶ E} {g : K ⟶ E}

/-- **The limit condition of Stacks 0EUW on a full subcategory passes to a fibre product of
functors.** -/
theorem preservesAffineLimitsOnSubcategory_of_isPullback (h : IsPullback p q f g)
    (hbB : PreservesAffineLimitsOnSubcategory P B)
    (hbK : PreservesAffineLimitsOnSubcategory P K)
    (hbE : PreservesAffineLimitsOnSubcategory P E) :
    PreservesAffineLimitsOnSubcategory P A := fun Λ _ _ _ D hD c hc =>
  nonempty_isColimit_mapCocone_of_isPullback D h c (hbB Λ D hD c hc).some
    (hbK Λ D hD c hc).some (hbE Λ D hD c hc).some

/-- The limit condition of Stacks 0EUW on a full subcategory transports along a natural
isomorphism. -/
theorem preservesAffineLimitsOnSubcategory_of_natIso {F G : P.FullSubcategoryᵒᵖ ⥤
    Type (max w (u + 1))} (e : F ≅ G) (hF : PreservesAffineLimitsOnSubcategory P F) :
    PreservesAffineLimitsOnSubcategory P G := fun Λ _ _ _ D hD c hc =>
  ⟨isColimit_mapCocone_of_natIso e c (hF Λ D hD c hc).some⟩

end SubcategoryPullback

end AlgebraicGeometry.ExtendingFunctors

end
