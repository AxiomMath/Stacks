module

public import Mathlib.RingTheory.Valuation.LocalSubring
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceCoincidenceLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdeals
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSupAffineSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupFlatBaseChange

/-!
# Coincidence along pairs of arcs

Let `C` and `L` be closed subspaces of an algebraic space `X` whose intersection `E = C ∩ L` is
an effective Cartier divisor, and let `c₁, c₂ : W ⟶ X` be morphisms from a Noetherian algebraic
space such that `c₁⁻¹ C ∩ c₂⁻¹ C ⊆ cᵢ⁻¹ L` for `i = 1, 2`. If `O ⊆ |W|` is open with `c₁(O)`,
`c₂(O)` disjoint from `|E|`, then every point `w` of the closure of `O` has one of `c₁ w`, `c₂ w`
in the coincidence locus of `C` and `E`.

This is the step of the repaired proof of Stacks 0F4B which shows that, after blowing up
`X₁` along `I + J ^ M`, no point of the closure of the off-diagonal part `O` of `U₁ ×_U U₁` has
both projections in the strict transform of the closure of `f⁻¹ Z₁` outside `V₁`: there
`C` is the pullback of that closure, `L` the pullback of `V(J ^ M)`, and `E` the exceptional
divisor.

The proof is local. On affine étale charts of `X` at `c₁ w` and `c₂ w` the divisor `E` is cut out
by `t_a` and `t_b`; an affine étale chart `G` of `W` at `w` maps to both. The scheme `G` is
Noetherian, so `w` is a specialization of a point of `O` there, and a valuation ring dominates the
specialization. Over a valuation ring the ideals are totally ordered, so along one of the two
arcs the ideals of `C` and `E` agree; the arc criterion
`AlgebraicGeometry.Space.mem_coincidenceLocus_of_mem_map` then puts that projection of `w` in the
coincidence locus.

## Main results

* `exists_mem_specializes_of_mem_closure_of_isOpen`: in a Noetherian quasi-sober space a point of
  the closure of an open set specializes from a point of it.
* `AlgebraicGeometry.Scheme.exists_valuationRing_of_specializes`: a specialization of points of a
  scheme is dominated by a valuation ring.
* `AlgebraicGeometry.Space.mem_coincidenceLocus_or_of_specializes`: the statement on charts.
* `AlgebraicGeometry.Space.mem_coincidenceLocus_or_of_mem_closure`: the statement above.

## References

* [Stacks Project, Tag 0F4B](https://stacks.math.columbia.edu/tag/0F4B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

/-- **In a Noetherian quasi-sober space a point of the closure of an open set is a
specialization of a point of the open set.** The closure is the union of the closures of the
finitely many irreducible closed pieces meeting the open set, and the generic point of each such
piece lies in the open set. -/
theorem exists_mem_specializes_of_mem_closure_of_isOpen {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] [QuasiSober X] {O : Set X} (hO : IsOpen O) {x : X}
    (hx : x ∈ closure O) : ∃ y ∈ O, y ⤳ x := by
  obtain ⟨T, hTfin, hTcl, hTirr, hT⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible (isClosed_closure (s := O))
  set T' := {t ∈ T | (t ∩ O).Nonempty}
  have hsub : O ⊆ ⋃₀ T' := by
    intro y hy
    obtain ⟨t, ht, hyt⟩ : y ∈ ⋃₀ T := hT ▸ subset_closure hy
    exact ⟨t, ⟨ht, y, hyt, hy⟩, hyt⟩
  have hcl : IsClosed (⋃₀ T') :=
    (hTfin.subset fun _ h => h.1).isClosed_sUnion fun t ht => hTcl t ht.1
  obtain ⟨t, ⟨htT, hne⟩, hxt⟩ := closure_minimal hsub hcl hx
  obtain ⟨y, hy⟩ := QuasiSober.sober (hTirr t htT) (hTcl t htT)
  exact ⟨y, (hy.mem_open_set_iff hO).2 hne, hy.specializes hxt⟩

namespace AlgebraicGeometry

/-- **A specialization of points of a scheme is dominated by a valuation ring.** For a
specialization `x ⤳ y` in a scheme `G` there are a valuation ring `A` and a ring map
`φ : Γ(G) ⟶ A` such that `φ r ≠ 0` when `x ∈ D(r)`, and `y ∈ D(r)` when `φ r` is a unit: the
generic point of `Spec A` goes to `x` and the closed point to `y`. The valuation ring is a
valuation subring of the residue field of `x` dominating the stalk at `y`. -/
theorem Scheme.exists_valuationRing_of_specializes (G : Scheme.{u}) {x y : G} (h : x ⤳ y) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A)
      (φ : Γ(G, ⊤) →+* A),
      (∀ r, x ∈ G.basicOpen r → φ r ≠ 0) ∧ (∀ r, IsUnit (φ r) → y ∈ G.basicOpen r) := by
  have hx : x ∈ (⊤ : G.Opens) := Set.mem_univ x
  have hy : y ∈ (⊤ : G.Opens) := Set.mem_univ y
  let f : G.presheaf.stalk y →+* G.residueField x :=
    (G.presheaf.stalkSpecializes h ≫ G.residue x).hom
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  let g : G.presheaf.stalk y →+* V := f.codRestrict V.toSubring hV
  refine ⟨V, inferInstance, inferInstance, inferInstance,
    g.comp (G.presheaf.germ ⊤ y hy).hom, fun r hr => ?_, fun r hr => ?_⟩
  · intro h0
    have h1 : f (G.presheaf.germ ⊤ y hy r) = 0 := congrArg Subtype.val h0
    have h2 : f (G.presheaf.germ ⊤ y hy r) =
        G.residue x (G.presheaf.germ ⊤ x hx r) := by
      show (G.presheaf.germ ⊤ y hy ≫ G.presheaf.stalkSpecializes h ≫ G.residue x) r = _
      rw [← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes]
      rfl
    rw [h2] at h1
    have hu : IsUnit (G.presheaf.germ ⊤ x hx r) := (G.mem_basicOpen (f := r) x hx).1 hr
    exact (hu.map (G.residue x).hom).ne_zero h1
  · have hu : IsUnit (G.presheaf.germ ⊤ y hy r) := (isUnit_map_iff g _).1 hr
    exact (G.mem_basicOpen (f := r) y hy).2 hu

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- On an affine étale chart, the global sections of the chart ideal sheaf of a closed subspace
are its defining ideal. -/
theorem chartKer_ideal_top_eq_definingIdealAt (Z : ClosedSubspaces B S hS X.1)
    (V : SmallEtale B S hS X.1) [IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left)] :
    (chartKer B S hS X Z V.1.hom).ideal ⟨⊤, isAffineOpen_top _⟩ =
      definingIdealAt B S hS X Z (op V) := by
  rw [chartKer_eq, ker_rep_snd_eq_ofIdealTop_definingIdealAt]
  exact Stacks.Divisors.ideal_ofIdealTop_top _ _

/-- On an affine étale chart, the global sections of the chart ideal sheaf of an intersection of
two closed subspaces are the sum of those of the two. -/
theorem chartKer_ideal_top_schemeTheoreticIntersection (C L : ClosedSubspaces B S hS X.1)
    (V : SmallEtale B S hS X.1) [IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left)] :
    (chartKer B S hS X (schemeTheoreticIntersection B S hS X.1 X.2 C L) V.1.hom).ideal
        ⟨⊤, isAffineOpen_top _⟩ =
      (chartKer B S hS X C V.1.hom).ideal ⟨⊤, isAffineOpen_top _⟩ ⊔
        (chartKer B S hS X L V.1.hom).ideal ⟨⊤, isAffineOpen_top _⟩ := by
  rw [chartKer_ideal_top_eq_definingIdealAt, chartKer_ideal_top_eq_definingIdealAt,
    chartKer_ideal_top_eq_definingIdealAt]
  exact definingIdealAt_inf_of_isAffine B S hS X C L (A := V)
    (show IsAffine (chartScheme V) from ‹IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left)›)

/-- **The coincidence criterion along a pair of arcs.** Let `C` and `L` be closed subspaces of
`X` with intersection `E = C ∩ L`, and let `V_a`, `V_b` be affine étale charts of `X` on which
`E` is cut out by `t_a` and `t_b`. Let `G` be a scheme with morphisms `m_a : G ⟶ V_a` and
`m_b : G ⟶ V_b` such that, on `G`, the pullback of `L` along either chart lies in the sum of the
pullbacks of `C` along both. If `x ⤳ y` is a specialization in `G` whose generic point avoids
the pullbacks of `E`, then one of `m_a y`, `m_b y` lies in the coincidence locus of `C` and `E`.

Over a valuation ring dominating the specialization, the ideals of `C` and of `E` along one of
the two arcs agree, because the ideals of a valuation ring are totally ordered; the arc criterion
`AlgebraicGeometry.Space.mem_coincidenceLocus_of_mem_map` concludes. -/
theorem mem_coincidenceLocus_or_of_specializes (C L : ClosedSubspaces B S hS X.1)
    (Va Vb : SmallEtale B S hS X.1) [IsAffine ((BigFppfOver.toScheme B S hS).obj Va.1.left)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Vb.1.left)] {ta tb}
    (hta : (chartKer B S hS X (schemeTheoreticIntersection B S hS X.1 X.2 C L) Va.1.hom).ideal
      ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {ta})
    (htb : (chartKer B S hS X (schemeTheoreticIntersection B S hS X.1 X.2 C L) Vb.1.hom).ideal
      ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {tb})
    {G : Scheme.{u}} (ma : G ⟶ (BigFppfOver.toScheme B S hS).obj Va.1.left)
    (mb : G ⟶ (BigFppfOver.toScheme B S hS).obj Vb.1.left)
    (hLa : ((chartKer B S hS X L Va.1.hom).ideal ⟨⊤, isAffineOpen_top _⟩).map ma.appTop.hom ≤
      ((chartKer B S hS X C Va.1.hom).ideal ⟨⊤, isAffineOpen_top _⟩).map ma.appTop.hom ⊔
        ((chartKer B S hS X C Vb.1.hom).ideal ⟨⊤, isAffineOpen_top _⟩).map mb.appTop.hom)
    (hLb : ((chartKer B S hS X L Vb.1.hom).ideal ⟨⊤, isAffineOpen_top _⟩).map mb.appTop.hom ≤
      ((chartKer B S hS X C Va.1.hom).ideal ⟨⊤, isAffineOpen_top _⟩).map ma.appTop.hom ⊔
        ((chartKer B S hS X C Vb.1.hom).ideal ⟨⊤, isAffineOpen_top _⟩).map mb.appTop.hom)
    {x y : G} (hxy : x ⤳ y)
    (hxa : ma x ∈ ((BigFppfOver.toScheme B S hS).obj Va.1.left).basicOpen ta)
    (hxb : mb x ∈ ((BigFppfOver.toScheme B S hS).obj Vb.1.left).basicOpen tb)
    (wa : points B S hS (yoneda.obj Va.1.left)) (hwa : pointsToScheme B S hS _ wa = ma y)
    (wb : points B S hS (yoneda.obj Vb.1.left)) (hwb : pointsToScheme B S hS _ wb = mb y) :
    pointsMap B S hS _ Va.1.hom wa ∈
        coincidenceLocus B S hS X C (schemeTheoreticIntersection B S hS X.1 X.2 C L) ∨
      pointsMap B S hS _ Vb.1.hom wb ∈
        coincidenceLocus B S hS X C (schemeTheoreticIntersection B S hS X.1 X.2 C L) := by
  obtain ⟨A, _, _, _, φ, hφ0, hφu⟩ := G.exists_valuationRing_of_specializes hxy
  have key : ∀ (V : SmallEtale B S hS X.1) [IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left)]
      (t : Γ((BigFppfOver.toScheme B S hS).obj V.1.left, ⊤))
      (_ : (chartKer B S hS X (schemeTheoreticIntersection B S hS X.1 X.2 C L) V.1.hom).ideal
        ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {t})
      (m : G ⟶ (BigFppfOver.toScheme B S hS).obj V.1.left)
      (_ : m x ∈ ((BigFppfOver.toScheme B S hS).obj V.1.left).basicOpen t)
      (w : points B S hS (yoneda.obj V.1.left)) (_ : pointsToScheme B S hS _ w = m y)
      (_ : (((chartKer B S hS X C V.1.hom).ideal ⟨⊤, isAffineOpen_top _⟩).map m.appTop.hom).map φ ⊔
          (((chartKer B S hS X L V.1.hom).ideal ⟨⊤, isAffineOpen_top _⟩).map m.appTop.hom).map φ =
        (((chartKer B S hS X C V.1.hom).ideal ⟨⊤, isAffineOpen_top _⟩).map m.appTop.hom).map φ),
      pointsMap B S hS _ V.1.hom w ∈
        coincidenceLocus B S hS X C (schemeTheoreticIntersection B S hS X.1 X.2 C L) := by
    intro V _ t ht m hm w hw hsup
    refine mem_coincidenceLocus_of_mem_map B S hS X C _ V.1.hom V.2 ht ?_
      (φ.comp m.appTop.hom) ?_ ?_ w ?_
    · rw [chartKer_ideal_top_schemeTheoreticIntersection]
      exact le_sup_left
    · refine IsLeftCancelMulZero.mul_left_cancel_of_ne_zero (hφ0 _ ?_)
      show x ∈ G.basicOpen (m.app ⊤ t)
      rw [← Scheme.preimage_basicOpen]
      exact hm
    · have e : Ideal.map (φ.comp m.appTop.hom)
            ((chartKer B S hS X C V.1.hom).ideal ⟨⊤, isAffineOpen_top _⟩) =
          Ideal.map (φ.comp m.appTop.hom) ((chartKer B S hS X
            (schemeTheoreticIntersection B S hS X.1 X.2 C L) V.1.hom).ideal
              ⟨⊤, isAffineOpen_top _⟩) := by
        rw [chartKer_ideal_top_schemeTheoreticIntersection, Ideal.map_sup,
          ← Ideal.map_map, ← Ideal.map_map, hsup]
      rw [e, ht]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self t)
    · intro r hr
      have : y ∈ G.basicOpen (m.app ⊤ r) := hφu _ hr
      rw [← Scheme.preimage_basicOpen] at this
      rwa [hw]
  have hNa := Ideal.map_mono (f := φ) hLa
  have hNb := Ideal.map_mono (f := φ) hLb
  rw [Ideal.map_sup] at hNa hNb
  rcases ValuationRing.sup_eq_left_or_sup_eq_left_of_le_sup hNa hNb with h | h
  · exact Or.inl (key Va ta hta ma hxa wa hwa h)
  · exact Or.inr (key Vb tb htb mb hxb wb hwb h)

section PointTopology

attribute [local instance] pointTopology

/-- **Pairs of points of a closed subspace off an effective Cartier divisor.** Let `C` and `L` be
closed subspaces of `X` whose intersection `E = C ∩ L` is an effective Cartier divisor. Let
`c₁, c₂ : W ⟶ X` be morphisms from a Noetherian algebraic space `W` such that the pullback of `L`
along either `cᵢ` contains `c₁⁻¹ C ∩ c₂⁻¹ C`. Let `O ⊆ |W|` be open with `c₁(O)` and `c₂(O)`
disjoint from `|E|`. Then for every `w` in the closure of `O`, one of `c₁ w`, `c₂ w` lies in the
coincidence locus of `C` and `E`.

The proof reads the situation on an affine étale chart of `W` lying over affine étale charts of
`X` at `c₁ w` and `c₂ w` on which `E` is principal; there `w` is a specialization of a point of
`O`, and `AlgebraicGeometry.Space.mem_coincidenceLocus_or_of_specializes` applies. -/
theorem mem_coincidenceLocus_or_of_mem_closure (hZ : B.Contains (⊤_ Scheme.{u}))
    {W : AlgebraicSpaces B S hS} (hN : IsNoetherian B S hS hZ W.1) (c₁ c₂ : W ⟶ X)
    (C L : ClosedSubspaces B S hS X.1)
    (hE : IsEffectiveCartierDivisor B S hS X (schemeTheoreticIntersection B S hS X.1 X.2 C L))
    (h₁ : (preimageClosedSubspace c₁ C).1 ⊓ (preimageClosedSubspace c₂ C).1 ≤
      (preimageClosedSubspace c₁ L).1)
    (h₂ : (preimageClosedSubspace c₁ C).1 ⊓ (preimageClosedSubspace c₂ C).1 ≤
      (preimageClosedSubspace c₂ L).1)
    {O : Set (points B S hS W.1)} (hO : IsOpen O)
    (hO₁ : ∀ o ∈ O, pointsMap B S hS _ c₁.hom o ∉
      subspacePointSet B S hS X.1 (schemeTheoreticIntersection B S hS X.1 X.2 C L).1)
    (hO₂ : ∀ o ∈ O, pointsMap B S hS _ c₂.hom o ∉
      subspacePointSet B S hS X.1 (schemeTheoreticIntersection B S hS X.1 X.2 C L).1)
    {w : points B S hS W.1} (hw : w ∈ closure O) :
    pointsMap B S hS _ c₁.hom w ∈
        coincidenceLocus B S hS X C (schemeTheoreticIntersection B S hS X.1 X.2 C L) ∨
      pointsMap B S hS _ c₂.hom w ∈
        coincidenceLocus B S hS X C (schemeTheoreticIntersection B S hS X.1 X.2 C L) := by
  classical
  set E := schemeTheoreticIntersection B S hS X.1 X.2 C L
  set T := BigFppfOver.toScheme B S hS
  have hpr := hasAffinePrincipalEtaleNeighborhoods_of_isEffectiveCartier B S hS X E hE
  obtain ⟨Va, va, haffa, hva, ta, -, hta⟩ :=
    exists_affine_chart_isRegular_span_of_hasAffinePrincipal B S hS X E hpr
      (pointsMap B S hS _ c₁.hom w)
  obtain ⟨Vb, vb, haffb, hvb, tb, -, htb⟩ :=
    exists_affine_chart_isRegular_span_of_hasAffinePrincipal B S hS X E hpr
      (pointsMap B S hS _ c₂.hom w)
  have hta' :=
    (chartKer_ideal_top_eq_definingIdealAt B S hS X E Va).trans hta
  have htb' :=
    (chartKer_ideal_top_eq_definingIdealAt B S hS X E Vb).trans htb
  obtain ⟨U₀, σ₀, hσs, hσe⟩ := W.2.exists_atlas
  obtain ⟨u₀, hu₀⟩ :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS W.1 W.2 U₀ σ₀).1 hσs w
  have hVa := Va.2
  set τa : yoneda.obj U₀ ⟶ X.1 := σ₀ ≫ c₁.hom with hτa
  obtain ⟨qa, hqa₁, hqa₂⟩ := exists_point_of_isPullback_presheaf B S hS
    (hVa.rep.isPullback' τa) va u₀ (by rw [hva, hτa, pointsMap_comp_apply, hu₀])
  have hVb := Vb.2
  set τb : yoneda.obj (hVa.rep.pullback τa) ⟶ X.1 :=
    yoneda.map (hVa.rep.snd τa) ≫ σ₀ ≫ c₂.hom with hτb
  obtain ⟨qab, hqab₁, hqab₂⟩ := exists_point_of_isPullback_presheaf B S hS
    (hVb.rep.isPullback' τb) vb qa
    (by rw [hvb, hτb, pointsMap_comp_apply, pointsMap_comp_apply, hqa₂, hu₀])
  let Q := hVb.rep.pullback τb
  let k : Q ⟶ U₀ := hVb.rep.snd τb ≫ hVa.rep.snd τa
  have hk : k = hVb.rep.snd τb ≫ hVa.rep.snd τa := rfl
  have hket : Etale (T.map k) := by
    rw [hk, Functor.map_comp]
    have h1 : Etale (T.map (hVb.rep.snd τb)) := hVb.property_snd τb
    have h2 : Etale (T.map (hVa.rep.snd τa)) := hVa.property_snd τa
    infer_instance
  let Gc : SmallEtale B S hS W.1 :=
    ⟨CostructuredArrow.mk (yoneda.map k ≫ σ₀), etale_comp_of_scheme B S hS k σ₀ hket hσe⟩
  obtain ⟨A, hA, hyA, -⟩ := exists_isAffineOpen_mem_and_subset
    (show pointsToScheme B S hS Q qab ∈ (⊤ : (T.obj Q).Opens) from trivial)
  let G₀ : SmallEtale B S hS W.1 := (chartOpens B S hS Gc).obj A
  have haff : IsAffine (T.obj G₀.1.left) := hA
  let ι : G₀.1.left ⟶ Q := chartOpenOverι B S hS Gc A
  have hG₀ : G₀.1.hom = yoneda.map ι ≫ yoneda.map k ≫ σ₀ := rfl
  let ma : G₀.1.left ⟶ Va.1.left := ι ≫ hVb.rep.snd τb ≫ hVa.rep.fst' τa
  let mb : G₀.1.left ⟶ Vb.1.left := ι ≫ hVb.rep.fst' τb
  have hpa : yoneda.map ma ≫ Va.1.hom = G₀.1.hom ≫ c₁.hom := by
    simp only [ma, hG₀, hk, Functor.map_comp, Category.assoc]
    rw [(hVa.rep.isPullback' τa).w]
  have hpb : yoneda.map mb ≫ Vb.1.hom = G₀.1.hom ≫ c₂.hom := by
    simp only [mb, hG₀, hk, Functor.map_comp, Category.assoc]
    rw [(hVb.rep.isPullback' τb).w]
  let g : T.obj G₀.1.left := ⟨pointsToScheme B S hS Q qab, hyA⟩
  let e := schemePointsHomeomorph B S hS G₀.1.left
  have he : ∀ z, pointsToScheme B S hS G₀.1.left (e.symm z) = z := fun z => by
    rw [← schemePointsHomeomorph_apply]
    exact e.apply_symm_apply z
  have hιT : T.map ι = A.ι := rfl
  have hwq : pointsMap B S hS _ (yoneda.map ι) (e.symm g) = qab := by
    apply injective_pointsToScheme B S hS Q
    rw [pointsToScheme_pointsMap_yoneda, he, hιT]
    rfl
  have hww : pointsMap B S hS _ G₀.1.hom (e.symm g) = w := by
    rw [hG₀, pointsMap_comp_apply, hwq, hk, Functor.map_comp, pointsMap_comp_apply,
      pointsMap_comp_apply, hqab₂, hqa₂, hu₀]
  have hcomp : ∀ (c : W ⟶ X) (V : SmallEtale B S hS X.1) (m : G₀.1.left ⟶ V.1.left)
      (_ : yoneda.map m ≫ V.1.hom = G₀.1.hom ≫ c.hom) (z),
      pointsMap B S hS _ c.hom (pointsMap B S hS _ G₀.1.hom z) =
        pointsMap B S hS _ V.1.hom (pointsMap B S hS _ (yoneda.map m) z) := fun c V m hm z => by
    rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, hm]
  set O'' : Set (T.obj G₀.1.left) := e.symm ⁻¹' (pointsMap B S hS _ G₀.1.hom ⁻¹' O) with hO''
  have hO''open : IsOpen O'' :=
    (hO.preimage (continuous_pointsMap B S hS G₀.1.hom)).preimage e.symm.continuous
  have hgcl : g ∈ closure O'' := by
    have h1 : e.symm g ∈ closure (pointsMap B S hS _ G₀.1.hom ⁻¹' O) :=
      (isOpenMap_pointsMap_of_presheafEtale B S hS _ G₀.2).preimage_closure_subset_closure_preimage
        (by rwa [Set.mem_preimage, hww])
    have h2 := (e.symm.preimage_closure (pointsMap B S hS _ G₀.1.hom ⁻¹' O)).symm ▸
      (show g ∈ e.symm ⁻¹' closure (pointsMap B S hS _ G₀.1.hom ⁻¹' O) from h1)
    exact h2
  have : IsLocallyNoetherian (T.obj G₀.1.left) :=
    (exists_atlas_iff_forall_etale B S hS W.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T)
      W.2).mp hN.2.2 G₀.1.left G₀.1.hom G₀.2
  have : AlgebraicGeometry.IsNoetherian (T.obj G₀.1.left) := {}
  obtain ⟨x, hxO, hxg⟩ := exists_mem_specializes_of_mem_closure_of_isOpen hO''open hgcl
  -- the generic point avoids `E` on both charts
  have hoff : ∀ (V : SmallEtale B S hS X.1) [IsAffine (T.obj V.1.left)] (t)
      (_ : (chartKer B S hS X E V.1.hom).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {t})
      (m : G₀.1.left ⟶ V.1.left),
      pointsMap B S hS _ V.1.hom (pointsMap B S hS _ (yoneda.map m) (e.symm x)) ∉
        subspacePointSet B S hS X.1 E.1 →
      T.map m x ∈ (T.obj V.1.left).basicOpen t := by
    intro V _ t ht m hx
    rw [mem_subspacePointSet_iff_mem_support_chartKer, pointsToScheme_pointsMap_yoneda, he,
      Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨⊤, isAffineOpen_top _⟩) trivial, ht]
      at hx
    by_contra hnot
    refine hx ((Scheme.mem_zeroLocus_iff _ _ _).2 fun f hf hfx => hnot ?_)
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hf
    rw [Scheme.basicOpen_mul] at hfx
    exact hfx.2
  have hxa := hoff Va ta hta' ma (by rw [← hcomp c₁ Va ma hpa]; exact hO₁ _ hxO)
  have hxb := hoff Vb tb htb' mb (by rw [← hcomp c₂ Vb mb hpb]; exact hO₂ _ hxO)
  -- the ideal inclusions on the chart
  have hinf := definingIdealAt_inf_of_isAffine B S hS W (preimageClosedSubspace c₁ C)
    (preimageClosedSubspace c₂ C) (A := G₀) haff
  have eC₁ := definingIdealAt_preimage_eq_map B S hS c₁ C Va G₀ ma hpa
  have eC₂ := definingIdealAt_preimage_eq_map B S hS c₂ C Vb G₀ mb hpb
  have key : ∀ (c : W ⟶ X) (V : SmallEtale B S hS X.1) [IsAffine (T.obj V.1.left)]
      (m : G₀.1.left ⟶ V.1.left) (hm : yoneda.map m ≫ V.1.hom = G₀.1.hom ≫ c.hom)
      (_ : (preimageClosedSubspace c₁ C).1 ⊓ (preimageClosedSubspace c₂ C).1 ≤
        (preimageClosedSubspace c L).1),
      ((chartKer B S hS X L V.1.hom).ideal ⟨⊤, isAffineOpen_top _⟩).map (T.map m).appTop.hom ≤
        ((chartKer B S hS X C Va.1.hom).ideal ⟨⊤, isAffineOpen_top _⟩).map (T.map ma).appTop.hom ⊔
          ((chartKer B S hS X C Vb.1.hom).ideal ⟨⊤, isAffineOpen_top _⟩).map
            (T.map mb).appTop.hom := by
    intro c V _ m hm hle
    have eL := definingIdealAt_preimage_eq_map B S hS c L V G₀ m hm
    have hanti := definingIdealAt_antitone B S hS W
      (schemeTheoreticIntersection B S hS W.1 W.2 (preimageClosedSubspace c₁ C)
        (preimageClosedSubspace c₂ C)) (preimageClosedSubspace c L) hle G₀
    have s1 : ((chartKer B S hS X L V.1.hom).ideal ⟨⊤, isAffineOpen_top _⟩).map
        (T.map m).appTop.hom = definingIdealAt B S hS W (preimageClosedSubspace c L) (op G₀) :=
      (congrArg _ (chartKer_ideal_top_eq_definingIdealAt B S hS X L V)).trans eL.symm
    have s2 : definingIdealAt B S hS W (schemeTheoreticIntersection B S hS W.1 W.2
        (preimageClosedSubspace c₁ C) (preimageClosedSubspace c₂ C)) (op G₀) =
        ((chartKer B S hS X C Va.1.hom).ideal ⟨⊤, isAffineOpen_top _⟩).map (T.map ma).appTop.hom ⊔
          ((chartKer B S hS X C Vb.1.hom).ideal ⟨⊤, isAffineOpen_top _⟩).map
            (T.map mb).appTop.hom := by
      rw [hinf]
      exact congrArg₂ (· ⊔ ·)
        (eC₁.trans (congrArg _ (chartKer_ideal_top_eq_definingIdealAt B S hS X C Va).symm))
        (eC₂.trans (congrArg _ (chartKer_ideal_top_eq_definingIdealAt B S hS X C Vb).symm))
    exact s1.le.trans (hanti.trans s2.le)
  have hLa := key c₁ Va ma hpa h₁
  have hLb := key c₂ Vb mb hpb h₂
  have hres := mem_coincidenceLocus_or_of_specializes B S hS X C L Va Vb hta' htb'
    (T.map ma) (T.map mb) hLa hLb hxg hxa hxb
    (pointsMap B S hS _ (yoneda.map ma) (e.symm g))
    (by rw [pointsToScheme_pointsMap_yoneda, he])
    (pointsMap B S hS _ (yoneda.map mb) (e.symm g))
    (by rw [pointsToScheme_pointsMap_yoneda, he])
  rwa [← hcomp c₁ Va ma hpa, ← hcomp c₂ Vb mb hpb, hww] at hres

end PointTopology

end Space

end AlgebraicGeometry

end
