module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.DirectedColimit
import all StacksFrontier.AlgebraicGeometry.FormalSpace.DirectedColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexed

/-!
# Directed colimits of affine formal algebraic spaces along thickenings

Let `D` be a directed system of affine formal algebraic spaces over `S` whose transition morphisms
are representable thickenings. Choosing a presentation of each member of the system and combining
their stages, the colimit of `D` is itself a directed colimit of affine schemes over `S` along
thickenings, with countable index whenever the system and all of its members are countably
indexed.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_affinePresentation_of_colimit'`: the colimit of such a
  system is a directed colimit of affine schemes over `S` along thickenings.

These results belong with `StacksFrontier.AlgebraicGeometry.FormalSpace.DirectedColimit` but are
kept in a module of their own, so that that module stays as it is on the base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w t v₁ v₂ u₁ u₂

namespace AlgebraicGeometry.FormalSpace

/-- Given presentations `Q i` of the members of the system `D`, the index type of the combined
presentation of the colimit: the disjoint union of the index types of the `Q i`. -/
private abbrev CombinedStageIndexOf (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type (u + 1)} [Preorder I]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (Q : ∀ i, AffinePresentation B S hS (D.obj i)) :=
  Σ i : I, (Q i).Index

/-- Given presentations `Q i` of the members of the system `D`, the affine scheme over `S`
indexed by a point of the combined index. -/
private def combinedStageObjectOf (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type (u + 1)} [Preorder I]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (Q : ∀ i, AffinePresentation B S hS (D.obj i))
    (p : CombinedStageIndexOf B S hS D Q) : BigAffineFppf B S hS :=
  let P := Q p.1
  letI : Preorder P.Index := P.preorder
  P.stages.obj p.2

/-- Given presentations `Q i` of the members of the system `D`, the morphism from a combined
stage to the colimit of `D`. -/
private def combinedStageMapToColimitOf (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {I : Type (u + 1)} [Preorder I]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (Q : ∀ i, AffinePresentation B S hS (D.obj i))
    (p : CombinedStageIndexOf B S hS D Q) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
      ((BigAffineFppf.inclusion B S hS).obj (combinedStageObjectOf B S hS D Q p)) ⟶
      colimit D := by
  let P := Q p.1
  letI : Preorder P.Index := P.preorder
  let F : P.Index ⥤ Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)) :=
    P.stages ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let eP : D.obj p.1 ≅ colimit F := Classical.choice P.comparison
  change F.obj p.2 ⟶ colimit D
  exact colimit.ι F p.2 ≫ eP.inv ≫ colimit.ι D p.1

/-- Given presentations `Q i` of the members of the system `D`, the morphism from a combined
stage to a sheaf `X` identified with the colimit of `D` by `e`. -/
private def combinedStageMapOf (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type (u + 1)} [Preorder I]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (Q : ∀ i, AffinePresentation B S hS (D.obj i))
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) (e : X ≅ colimit D)
    (p : CombinedStageIndexOf B S hS D Q) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
      ((BigAffineFppf.inclusion B S hS).obj (combinedStageObjectOf B S hS D Q p)) ⟶ X :=
  combinedStageMapToColimitOf B S hS D Q p ≫ e.inv

/-- The map from a combined stage `p` to the colimit of `D` factors through `D.obj k` for
`p.1 ≤ k`. -/
private theorem stageMap_comp_map_comp_colimit_ι (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {I : Type (u + 1)} [Preorder I]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (Q : ∀ i, AffinePresentation B S hS (D.obj i)) (p : CombinedStageIndexOf B S hS D Q) {k : I}
    (hpk : p.1 ≤ k) :
    (affinePresentationStageMap B S hS (D.obj p.1) (Q p.1) p.2 ≫ D.map (homOfLE hpk)) ≫
      colimit.ι D k = combinedStageMapToColimitOf B S hS D Q p :=
  (Category.assoc _ _ _).trans
    (congrArg (affinePresentationStageMap B S hS _ (Q p.1) p.2 ≫ ·) (colimit.w D (homOfLE hpk)))

/-- A factorization of the map from a combined stage `p` to `D.obj k` through a stage `i` of
`Q k` gives, for every later stage `n`, a morphism of combined stages `p ⟶ ⟨k, n⟩` compatible
with their maps to `X`. -/
private theorem combinedStageMapOf_comp_of_factor (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {I : Type (u + 1)} [Preorder I]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (Q : ∀ i, AffinePresentation B S hS (D.obj i))
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) (e : X ≅ colimit D)
    (p : CombinedStageIndexOf B S hS D Q) {k : I} (hpk : p.1 ≤ k) :
    letI : Preorder (Q k).Index := (Q k).preorder
    ∀ {i n : (Q k).Index} (hin : i ≤ n)
      (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
          ((BigAffineFppf.inclusion B S hS).obj (combinedStageObjectOf B S hS D Q p)) ⟶
        ((Q k).stages ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj i),
      g ≫ colimit.ι ((Q k).stages ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫
          (Classical.choice (Q k).comparison).inv =
        affinePresentationStageMap B S hS (D.obj p.1) (Q p.1) p.2 ≫ D.map (homOfLE hpk) →
      (g ≫ ((Q k).stages ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (homOfLE hin)) ≫
        combinedStageMapOf B S hS D Q X e ⟨k, n⟩ = combinedStageMapOf B S hS D Q X e p := by
  let : Preorder (Q k).Index := (Q k).preorder
  intro i n hin g hg
  change g ≫ (((Q k).stages ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map (homOfLE hin) ≫
      colimit.ι ((Q k).stages ⋙ BigAffineFppf.inclusion B S hS ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) n) ≫
      (Classical.choice (Q k).comparison).inv ≫ colimit.ι D k ≫ e.inv = _
  rw [colimit.w]
  rw [(reassoc_of% hg), combinedStageMapOf,
    ← stageMap_comp_map_comp_colimit_ι B S hS D Q p hpk]
  exact (Category.assoc _ _ _).symm

/-- Given presentations `Q i` of the members of the system `D`, any two combined stages admit
morphisms to a third combined stage compatible with their maps to `X`. -/
private theorem combinedStage_exists_upperOf (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (Q : ∀ i, AffinePresentation B S hS (D.obj i))
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) (e : X ≅ colimit D)
    (p q : CombinedStageIndexOf B S hS D Q) :
    ∃ r : CombinedStageIndexOf B S hS D Q,
      (∃ f : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
          ((BigAffineFppf.inclusion B S hS).obj (combinedStageObjectOf B S hS D Q p)) ⟶
          (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
            ((BigAffineFppf.inclusion B S hS).obj (combinedStageObjectOf B S hS D Q r)),
        f ≫ combinedStageMapOf B S hS D Q X e r = combinedStageMapOf B S hS D Q X e p) ∧
      (∃ f : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
          ((BigAffineFppf.inclusion B S hS).obj (combinedStageObjectOf B S hS D Q q)) ⟶
          (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
            ((BigAffineFppf.inclusion B S hS).obj (combinedStageObjectOf B S hS D Q r)),
        f ≫ combinedStageMapOf B S hS D Q X e r = combinedStageMapOf B S hS D Q X e q) := by
  classical
  obtain ⟨k, hpk, hqk⟩ := exists_ge_ge p.1 q.1
  let Pk := Q k
  let : Preorder Pk.Index := Pk.preorder
  let : Nonempty Pk.Index := Pk.nonempty
  let : IsDirected Pk.Index (· ≤ ·) := Pk.directed
  let ePk : D.obj k ≅ colimit (Pk.stages ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) := Classical.choice Pk.comparison
  obtain ⟨ip, gp, hgp⟩ := exists_factor_affine_through_presentation
    B S hS Pk.stages Pk.stageThickenings (D.obj k) ePk (combinedStageObjectOf B S hS D Q p)
    (affinePresentationStageMap B S hS (D.obj p.1) (Q p.1) p.2 ≫ D.map (homOfLE hpk))
  obtain ⟨iq, gq, hgq⟩ := exists_factor_affine_through_presentation
    B S hS Pk.stages Pk.stageThickenings (D.obj k) ePk (combinedStageObjectOf B S hS D Q q)
    (affinePresentationStageMap B S hS (D.obj q.1) (Q q.1) q.2 ≫ D.map (homOfLE hqk))
  obtain ⟨n, hpn, hqn⟩ := exists_ge_ge ip iq
  exact ⟨⟨k, n⟩, ⟨_, combinedStageMapOf_comp_of_factor B S hS D Q X e p hpk hpn gp hgp⟩,
    ⟨_, combinedStageMapOf_comp_of_factor B S hS D Q X e q hqk hqn gq hgq⟩⟩

/-- The presentation that prefers a countable index type has one as soon as *some*
presentation does. -/
private theorem countable_index_affinePresentation (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hc : ∃ P : AffinePresentation B S hS X, Countable P.Index) :
    Countable (open Classical in
      if hc : ∃ P : AffinePresentation B S hS X, Countable P.Index then hc.choose
      else affinePresentation B S hS X hX).Index := by
  classical
  rw [dite_eq_left hc]
  exact hc.choose_spec

/-- A countably indexed sheaf admits an affine presentation with countable index type. -/
private theorem exists_countable_index_affinePresentation (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (hX : IsCountablyIndexed B S hS X) :
    ∃ P : AffinePresentation B S hS X, Countable P.Index := by
  obtain ⟨D, hthick, hcolim⟩ := hX
  have hd : Monotone (ULift.down : ULift.{u + 1, 0} ℕ → ℕ) := fun _ _ h => h
  let e := hd.functor
  have : Functor.Final e := hd.final_functor_iff.mpr fun n => ⟨ULift.up n, le_rfl⟩
  refine ⟨⟨ULift.{u + 1, 0} ℕ, inferInstance, ⟨ULift.up 0⟩, inferInstance, e ⋙ D,
    fun ⦃_ _⦄ f => hthick (e.map f), ?_⟩, inferInstance⟩
  exact hcolim.map fun k => k ≪≫ (Functor.Final.colimitIso e _).symm

/-- The map from a combined stage to the colimit of `D` is a monomorphism. -/
private theorem mono_combinedStageMapToColimitOf (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (hthick : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
        (MorphismProperty.inverseImage
          (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) (D.map f))
    (Q : ∀ i, AffinePresentation B S hS (D.obj i)) (p : CombinedStageIndexOf B S hS D Q) :
    Mono (combinedStageMapToColimitOf B S hS D Q p) := by
  have : ∀ i j (f : i ⟶ j), Mono (D.map f) :=
    fun _ _ f => mono_of_relativeThickening B S hS (hthick f)
  have := affinePresentationStageMap_mono B S hS (D.obj p.1) (Q p.1) p.2
  have := mono_colimit_ι B S hS D p.1
  change Mono (affinePresentationStageMap B S hS (D.obj p.1) (Q p.1) p.2 ≫ colimit.ι D p.1)
  infer_instance

/-- The transition morphisms of the factorization diagram of the combined stages are
representable thickenings. -/
private theorem relative_isThickening_combinedFactorizationDiagram_map (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {I : Type (u + 1)} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (hthick : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
        (MorphismProperty.inverseImage
          (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) (D.map f))
    (Q : ∀ i, AffinePresentation B S hS (D.obj i)) :
    haveI := mono_combinedStageMapToColimitOf B S hS D hthick Q
    letI := factorizationPreorder _ (combinedStageMapToColimitOf B S hS D Q)
    ∀ ⦃p q : CombinedStageIndexOf B S hS D Q⦄ (f : p ⟶ q),
      MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
        (MorphismProperty.inverseImage
          (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))
        ((factorizationDiagram _ (combinedStageMapToColimitOf B S hS D Q)).map f) := by
  have := mono_combinedStageMapToColimitOf B S hS D hthick Q
  let := factorizationPreorder _ (combinedStageMapToColimitOf B S hS D Q)
  intro p q f
  have : ∀ i j (f : i ⟶ j), Mono (D.map f) :=
    fun _ _ f => mono_of_relativeThickening B S hS (hthick f)
  obtain ⟨k, hpk, hqk⟩ := exists_ge_ge p.1 q.1
  let Th := MorphismProperty.inverseImage
    (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)
  let := MorphismProperty.IsStableUnderComposition.inverseImage
    (P := (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}))
    (BigFppfOver.toScheme B S hS)
  let b (r : CombinedStageIndexOf B S hS D Q) (hr : r.1 ≤ k) :
      (factorizationDiagram _ (combinedStageMapToColimitOf B S hS D Q)).obj r ⟶ D.obj k :=
    affinePresentationStageMap B S hS _ (Q r.1) r.2 ≫ D.map (homOfLE hr)
  have hb (r : CombinedStageIndexOf B S hS D Q) (hr : r.1 ≤ k) :
      b r hr ≫ colimit.ι D k = combinedStageMapToColimitOf B S hS D Q r :=
    stageMap_comp_map_comp_colimit_ι B S hS D Q r hr
  have hbp : Th.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (b p hpk) :=
    (Th.relative _).comp_mem _ _
      (affinePresentationStageMap_relativeThickening B S hS _ (Q p.1) p.2) (hthick _)
  have : Mono (b q hqk ≫ colimit.ι D k) := by
    rw [hb q hqk]
    exact mono_combinedStageMapToColimitOf B S hS D hthick Q q
  have : Mono (b q hqk) := mono_of_mono _ (colimit.ι D k)
  have heq : (factorizationDiagram _ (combinedStageMapToColimitOf B S hS D Q)).map f ≫ b q hqk =
      b p hpk := by
    have := mono_colimit_ι B S hS D k
    apply (cancel_mono (colimit.ι D k)).mp
    rw [Category.assoc, hb q hqk, hb p hpk]
    exact factorizationDiagram_map _ _ f
  have hpull : IsPullback (𝟙 _)
      ((factorizationDiagram _ (combinedStageMapToColimitOf B S hS D Q)).map f) (b p hpk)
      (b q hqk) :=
    IsPullback.of_horiz_isIso_mono ⟨(Category.id_comp _).trans heq.symm⟩
  exact Th.relative_isStableUnderBaseChange.of_isPullback hpull hbp

/-- The combined presentation of the colimit by the sheaves represented by the stages of the
presentations of the members of the system. -/
private theorem exists_combinedPresentation' (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (hD : ∀ i, IsAffineFormalAlgebraicSpace B S hS (D.obj i))
    (hthick : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
        (MorphismProperty.inverseImage
          (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) (D.map f))
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) (e : X ≅ colimit D) :
    ∃ (K : Type (u + 1)) (pre : Preorder K), letI := pre
      Nonempty K ∧ IsDirected K (· ≤ ·) ∧
      (Countable I → (∀ i, IsCountablyIndexed B S hS (D.obj i)) → Countable K) ∧
      ∃ (F : K ⥤ Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
        (A : K → BigAffineFppf B S hS),
        (∀ p, F.obj p = (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
          ((BigAffineFppf.inclusion B S hS).obj (A p))) ∧
        (∀ ⦃p q : K⦄ (f : p ⟶ q),
          MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
            (MorphismProperty.inverseImage
              (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
              (BigFppfOver.toScheme B S hS)) (F.map f)) ∧
        Nonempty (X ≅ colimit F) := by
  classical
  let P i : AffinePresentation B S hS (D.obj i) :=
    if hc : ∃ P : AffinePresentation B S hS (D.obj i), Countable P.Index then hc.choose
    else affinePresentation B S hS (D.obj i) (hD i)
  let (i : I) : Preorder (P i).Index := (P i).preorder
  let (i : I) : Nonempty (P i).Index := (P i).nonempty
  let (i : I) : IsDirected (P i).Index (· ≤ ·) := (P i).directed
  let K := CombinedStageIndexOf B S hS D P
  let T (i : I) := affinePresentationSheafDiagram B S hS (D.obj i) (P i)
  let s (i : I) : T i ⟶ (Functor.const (P i).Index).obj (D.obj i) := {
    app := affinePresentationStageMap B S hS (D.obj i) (P i)
    naturality := fun p q f => by
      simpa using affinePresentationStageMap_fac B S hS (D.obj i) (P i) f }
  have hs (i : I) : IsColimit (Cocone.mk (D.obj i) (s i)) :=
    (colimit.isColimit (T i)).ofIsoColimit
      (Cocone.ext (affinePresentationComparison B S hS (D.obj i) (P i)).symm
        fun _ => by simp [s, affinePresentationStageMap, T])
  let a : ∀ p : K, (T p.1).obj p.2 ⟶ colimit D := combinedStageMapToColimitOf B S hS D P
  have : ∀ p : K, Mono (a p) := mono_combinedStageMapToColimitOf B S hS D hthick P
  let A := fun p : K => (T p.1).obj p.2
  let : Preorder K := factorizationPreorder A a
  let : LE K := (factorizationPreorder A a).toLE
  let : SmallCategory K := Preorder.smallCategory _
  let F := factorizationDiagram A a
  have hdir : IsDirected K (· ≤ ·) := ⟨fun p q => by
    obtain ⟨r, ⟨g, hg⟩, ⟨g', hg'⟩⟩ :=
      combinedStage_exists_upperOf B S hS D P (colimit D) (Iso.refl _) p q
    change A p ⟶ A r at g
    change A q ⟶ A r at g'
    change g ≫ (a r ≫ 𝟙 _) = a p ≫ 𝟙 _ at hg
    change g' ≫ (a r ≫ 𝟙 _) = a q ≫ 𝟙 _ at hg'
    exact ⟨r, ⟨g, by simpa only [Category.comp_id] using hg⟩,
      ⟨g', by simpa only [Category.comp_id] using hg'⟩⟩⟩
  have hc : IsColimit (factorizationCocone A a) :=
    isColimit_factorizationCocone D (colimit.cocone D) (colimit.isColimit D)
      (fun i => (P i).Index) T s hs a (fun _ => rfl) fun {i j} f x =>
        exists_factor_affine_through_presentation B S hS (P j).stages (P j).stageThickenings
          (D.obj j) (affinePresentationComparison B S hS (D.obj j) (P j)) ((P i).stages.obj x)
          ((s i).app x ≫ D.map f)
  have hcnt : Countable I → (∀ i, IsCountablyIndexed B S hS (D.obj i)) → Countable K := by
    intro hI hstage
    have : ∀ i, Countable (P i).Index := fun i =>
      countable_index_affinePresentation B S hS (D.obj i) (hD i)
        (exists_countable_index_affinePresentation B S hS (D.obj i) (hstage i))
    exact inferInstanceAs (Countable (Σ i : I, (P i).Index))
  exact ⟨K, inferInstance, ⟨⟨Classical.arbitrary I, Classical.arbitrary _⟩⟩, hdir, hcnt, F,
    combinedStageObjectOf B S hS D P, fun _ => rfl,
    relative_isThickening_combinedFactorizationDiagram_map B S hS D hthick P,
    ⟨e.trans (hc.coconePointUniqueUpToIso (colimit.isColimit F))⟩⟩

/-- The colimit of a directed system of affine formal algebraic spaces over `S` whose
transition morphisms are representable thickenings is a directed colimit of affine schemes
over `S` along thickenings. -/
theorem exists_affinePresentation_of_colimit' (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (hD : ∀ i, IsAffineFormalAlgebraicSpace B S hS (D.obj i))
    (hthick : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
        (MorphismProperty.inverseImage
          (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) (D.map f))
    (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) (e : X ≅ colimit D) :
    ∃ (K : Type (u + 1)) (pre : Preorder K), letI := pre
      Nonempty K ∧ IsDirected K (· ≤ ·) ∧
      (Countable I → (∀ i, IsCountablyIndexed B S hS (D.obj i)) → Countable K) ∧
      ∃ F : K ⥤ BigAffineFppf B S hS,
        (∀ ⦃p q : K⦄ (f : p ⟶ q), Stacks.Thickenings.IsThickening
          ((BigAffineFppf.toScheme B S hS).map (F.map f))) ∧
        Nonempty (X ≅ colimit (F ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) := by
  obtain ⟨K, pre, hne, hdir, hcnt, F, A, hA, hF, ⟨eF⟩⟩ :=
    exists_combinedPresentation' B S hS D hD hthick X e
  let : Preorder K := pre
  let ff := fullyFaithful_sheafifiedYoneda B S hS
  let := ff.full
  let := ff.faithful
  let Y := BigAffineFppf.inclusion B S hS ⋙
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  obtain ⟨G, ⟨eG⟩⟩ := exists_liftDiagram Y F A hA
  refine ⟨K, pre, hne, hdir, hcnt, G, ?_, ⟨eF.trans (HasColimit.isoOfNatIso eG.symm)⟩⟩
  intro p q f
  let Q := MorphismProperty.inverseImage
    (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have hg : Q.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) (Y.map (G.map f)) :=
    (MorphismProperty.arrow_mk_iso_iff (P := Q.relative _)
      (Arrow.isoMk (eG.app p) (eG.app q) (eG.hom.naturality f).symm)).mpr (hF f)
  exact hg.property (𝟙 _) (𝟙 _)
    ((BigAffineFppf.inclusion B S hS).map (G.map f)) IsPullback.of_id_fst

end AlgebraicGeometry.FormalSpace

end
