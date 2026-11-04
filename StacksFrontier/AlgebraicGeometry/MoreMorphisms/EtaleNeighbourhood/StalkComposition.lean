module

public import StacksFrontier.AlgebraicGeometry.Etale.NeighborhoodStalkFiber
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.EtaleNeighbourhood.FiberLifting
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ResidueFieldMap

/-!
# Composing an étale neighbourhood of a point with one of its local scheme

Let `V` be an elementary étale neighbourhood of a point `s` of a scheme `S` and let `W` be an
elementary étale neighbourhood of the closed point of the local scheme `Spec 𝒪_{V, v}`. Then there
is a *single* elementary étale neighbourhood `U` of `(S, s)` whose local scheme `Spec 𝒪_{U, u}`
maps to `Spec 𝒪_{W, w}` over `S`, carrying closed point to closed point.

## Main results

* `AlgebraicGeometry.EtaleNeighborhood.exists_isElementary_specStalkHom_of_fromSpecStalk_eq`: the
  composition, for a neighbourhood of an arbitrary point of `Spec 𝒪_{V, v}` lying over `v`.
* `AlgebraicGeometry.EtaleNeighborhood.exists_isElementary_specStalkHom`: the same at the closed
  point.

## References

* [Stacks Project, Tag 02LE](https://stacks.math.columbia.edu/tag/02LE)
* [Stacks Project, Tag 05I5](https://stacks.math.columbia.edu/tag/05I5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

/-- `AlgebraicGeometry.Scheme.fromSpecStalk` is compatible with transporting the stalk along an
equality of points. -/
private lemma specMap_eqToHom_fromSpecStalk {X : Scheme.{u}} {x y : X} (h : x = y)
    (e : X.presheaf.stalk x = X.presheaf.stalk y) :
    Spec.map (eqToHom e) ≫ X.fromSpecStalk x = X.fromSpecStalk y := by
  subst h
  simp

/-- A morphism from a local scheme sending the closed point to `x` factors through
`X.fromSpecStalk x`. -/
private lemma Scheme.exists_comp_fromSpecStalk_eq {X : Scheme.{u}} {R : CommRingCat.{u}}
    [IsLocalRing R] (q : Spec R ⟶ X) {x : X} (h : q (closedPoint R) = x) :
    ∃ β : Spec R ⟶ Spec (X.presheaf.stalk x), β ≫ X.fromSpecStalk x = q := by
  subst h
  exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk q⟩

/-- If `f` is a preimmersion and `f ≫ g` induces an isomorphism on residue fields at `x`, then so
does `g` at `f x`. -/
private lemma Scheme.Hom.isIso_residueFieldMap_of_isPreimmersion_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) [IsPreimmersion f] (g : Y ⟶ Z) (x : X) (h : IsIso ((f ≫ g).residueFieldMap x)) :
    IsIso (g.residueFieldMap (f x)) := by
  rw [Scheme.residueFieldMap_comp] at h
  have hf : IsIso (f.residueFieldMap x) := isIso_residueFieldMap_of_isPreimmersion _ _
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ (f.residueFieldMap x) hf h

/-- An étale scheme over the local scheme `Spec 𝒪_{X, x}` of a point `x` of an affine open `V₀`
descends to an étale `Γ(X, V₀)`-algebra, as a pullback square of affine schemes. -/
private theorem exists_etale_isPullback_germ {X : Scheme.{u}} {V₀ : X.Opens} (hV₀ : IsAffineOpen V₀)
    {x : X} (hx : x ∈ V₀) {T : CommRingCat.{u}} (g : Spec T ⟶ Spec (X.presheaf.stalk x))
    [Etale g] :
    ∃ (E : CommRingCat.{u}) (a : Γ(X, V₀) ⟶ E) (b : E ⟶ T), Etale (Spec.map a) ∧
      IsPreimmersion (Spec.map b) ∧
      IsPullback g (Spec.map b) (Spec.map (X.presheaf.germ V₀ x hx)) (Spec.map a) := by
  let A := Γ(X, V₀)
  let L := X.presheaf.stalk x
  let germ : A ⟶ L := X.presheaf.germ V₀ x hx
  let : Algebra A L := germ.hom.toAlgebra
  let M := (hV₀.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  let : IsLocalization M L := hV₀.isLocalization_stalk ⟨x, hx⟩
  have halg : CommRingCat.ofHom (algebraMap A L) = germ := rfl
  let c : L ⟶ T := Spec.preimage g
  have hcg : Spec.map c = g := Spec.map_preimage g
  have hc : CommRingCat.etale c :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp (hcg ▸ inferInstance)
  obtain ⟨E, a, b, ha, hpo⟩ := exists_etale_pushout_of_localization A L T M c.hom hc
  have hpo' : IsPushout germ a c b := by rwa [← halg, ← CommRingCat.ofHom_hom c]
  have hpb : IsPullback g (Spec.map b) (Spec.map germ) (Spec.map a) := by
    rw [← hcg]
    exact isPullback_SpecMap_of_isPushout _ _ _ _ hpo'
  have hpreGerm : IsPreimmersion (Spec.map germ) := halg ▸ IsPreimmersion.of_isLocalization M
  exact ⟨E, a, b, (HasRingHomProperty.Spec_iff (P := @Etale)).mpr ha,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb hpreGerm, hpb⟩

/-- A morphism from a local scheme to the bottom-right corner of a pullback of
`Spec 𝒪_{X, x} ⟶ Y`, whose image in `X` sends the closed point to `x`, lifts to the pullback. -/
private theorem exists_lift_of_isPullback_fromSpecStalk {X Y E P : Scheme.{u}} {x : X}
    {ι : Spec (X.presheaf.stalk x) ⟶ Y} {j : Y ⟶ X} [Mono j] (hιj : ι ≫ j = X.fromSpecStalk x)
    {g : P ⟶ Spec (X.presheaf.stalk x)} {b : P ⟶ E} {a : E ⟶ Y} (hpb : IsPullback g b ι a)
    {R : CommRingCat.{u}} [IsLocalRing R] (p : Spec R ⟶ E) (hp : (p ≫ a ≫ j) (closedPoint R) = x) :
    ∃ κ : Spec R ⟶ P, κ ≫ b = p ∧ κ ≫ g ≫ X.fromSpecStalk x = p ≫ a ≫ j := by
  obtain ⟨β, hβ⟩ := Scheme.exists_comp_fromSpecStalk_eq (p ≫ a ≫ j) hp
  have hβι : β ≫ ι = p ≫ a := by
    rw [← cancel_mono j, Category.assoc, Category.assoc, hιj, hβ]
  exact ⟨hpb.lift β p hβι, hpb.lift_snd _ _ _, by rw [reassoc_of% (hpb.lift_fst β p hβι), hβ]⟩

namespace EtaleNeighborhood

/-- For an elementary étale neighbourhood `W` of a point `z` of `Spec 𝒪_{V, v}` over `v`, the
composite `W ⟶ S` induces an isomorphism on residue fields at the distinguished point of `W`. -/
private theorem isIso_residueFieldMap_toBase_comp_fromSpecStalk {S : Scheme.{u}} {s : S}
    (V : EtaleNeighborhood S s) (hV : V.IsElementary)
    {z : ↥(Spec (V.scheme.presheaf.stalk V.point))}
    (hz : V.scheme.fromSpecStalk V.point z = V.point)
    (W : EtaleNeighborhood (Spec (V.scheme.presheaf.stalk V.point)) z) (hW : W.IsElementary) :
    IsIso ((W.toBase ≫ V.scheme.fromSpecStalk V.point ≫ V.toBase).residueFieldMap W.point) := by
  have hpt : V.scheme.fromSpecStalk V.point (W.toBase W.point) = V.point := by
    rw [W.map_point, hz]
  have h₂ : IsIso (W.toBase.residueFieldMap W.point) := (isElementary_iff W).mp hW
  have h₃ : IsIso ((V.scheme.fromSpecStalk V.point).residueFieldMap (W.toBase W.point)) :=
    isIso_residueFieldMap_of_isPreimmersion _ _
  have h₄ : IsIso (V.toBase.residueFieldMap
      (V.scheme.fromSpecStalk V.point (W.toBase W.point))) :=
    (V.toBase.isIso_residueFieldMap_congr hpt).mpr ((isElementary_iff V).mp hV)
  rw [Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp]
  exact IsIso.comp_isIso' (IsIso.comp_isIso' h₄ h₃) h₂

/-- **Composing an étale neighbourhood with an étale neighbourhood of its local scheme.** Let `V`
be an elementary étale neighbourhood of `(S, s)`, let `z` be a point of `Spec 𝒪_{V, v}` lying over
the distinguished point `v`, and let `W` be an elementary étale neighbourhood of
`(Spec 𝒪_{V, v}, z)`. Then there are an elementary étale neighbourhood `U` of `(S, s)` and a
morphism `Spec 𝒪_{U, u} ⟶ Spec 𝒪_{W, w}` over `S` which carries the closed point to the closed
point. -/
theorem exists_isElementary_specStalkHom_of_fromSpecStalk_eq {S : Scheme.{u}} {s : S}
    (V : EtaleNeighborhood S s) (hV : V.IsElementary)
    {z : ↥(Spec (V.scheme.presheaf.stalk V.point))}
    (hz : V.scheme.fromSpecStalk V.point z = V.point)
    (W : EtaleNeighborhood (Spec (V.scheme.presheaf.stalk V.point)) z) (hW : W.IsElementary) :
    ∃ (U : EtaleNeighborhood S s) (_ : U.IsElementary)
      (φ : Spec (U.scheme.presheaf.stalk U.point) ⟶
            Spec (W.scheme.presheaf.stalk W.point)),
      φ (closedPoint (U.scheme.presheaf.stalk U.point)) =
          closedPoint (W.scheme.presheaf.stalk W.point) ∧
      φ ≫ W.scheme.fromSpecStalk W.point ≫ W.toBase ≫
            V.scheme.fromSpecStalk V.point ≫ V.toBase
          = U.scheme.fromSpecStalk U.point ≫ U.toBase := by
  obtain ⟨V₀, hV₀, hvV₀, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := V.scheme) (x := V.point) (U := ⊤) trivial
  obtain ⟨W₀, hW₀, hwW₀, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := W.scheme) (x := W.point) (U := ⊤) trivial
  let g : Spec Γ(W.scheme, W₀) ⟶ Spec (V.scheme.presheaf.stalk V.point) := hW₀.fromSpec ≫ W.toBase
  obtain ⟨E, a, b, _, _, hpb⟩ := exists_etale_isPullback_germ hV₀ hvV₀ g
  have hgf : Spec.map (V.scheme.presheaf.germ V₀ V.point hvV₀) ≫ hV₀.fromSpec =
      V.scheme.fromSpecStalk V.point := hV₀.fromSpecStalk_eq_fromSpecStalk hvV₀
  obtain ⟨wT, hwT⟩ : W.point ∈ Set.range hW₀.fromSpec := by
    rwa [hW₀.range_fromSpec]
  have hbase : Spec.map b ≫ Spec.map a ≫ hV₀.fromSpec =
      hW₀.fromSpec ≫ W.toBase ≫ V.scheme.fromSpecStalk V.point := by
    rw [← Category.assoc (Spec.map b), ← hpb.w, ← hgf]
    simp only [g, Category.assoc]
  have hau : (Spec.map a ≫ hV₀.fromSpec) (Spec.map b wT) = V.point := by
    rw [← Scheme.Hom.comp_apply, hbase]
    simp only [Scheme.Hom.comp_apply, hwT, W.map_point, hz]
  let U : EtaleNeighborhood S s :=
    { scheme := Spec E
      point := Spec.map b wT
      toBase := Spec.map a ≫ hV₀.fromSpec ≫ V.toBase
      map_point := by rw [← Category.assoc, Scheme.Hom.comp_apply, hau, V.map_point] }
  have hUres : IsIso (U.toBase.residueFieldMap (Spec.map b wT)) := by
    refine Scheme.Hom.isIso_residueFieldMap_of_isPreimmersion_comp (Spec.map b) U.toBase wT ?_
    show IsIso ((Spec.map b ≫ (Spec.map a ≫ hV₀.fromSpec ≫ V.toBase)).residueFieldMap wT)
    rw [reassoc_of% hbase, Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' ((Scheme.Hom.isIso_residueFieldMap_congr _ hwT).mpr
      (isIso_residueFieldMap_toBase_comp_fromSpecStalk V hV hz W hW))
      (isIso_residueFieldMap_of_isPreimmersion _ _)
  let pU : Spec (U.scheme.presheaf.stalk U.point) ⟶ Spec E := U.scheme.fromSpecStalk U.point
  let cP : ↥(Spec (U.scheme.presheaf.stalk U.point)) := closedPoint _
  have hpUcP : pU cP = Spec.map b wT := Scheme.fromSpecStalk_closedPoint
  obtain ⟨κ, hκb, hκ⟩ := exists_lift_of_isPullback_fromSpecStalk hgf hpb pU (by
    show (pU ≫ Spec.map a ≫ hV₀.fromSpec) cP = V.point
    rw [Scheme.Hom.comp_apply, hpUcP, hau])
  have hκcP : κ cP = wT := by
    refine (Spec.map b).isEmbedding.injective ?_
    rw [← Scheme.Hom.comp_apply, hκb, hpUcP]
  have hκW : (κ ≫ hW₀.fromSpec) cP = W.point := by rw [Scheme.Hom.comp_apply, hκcP, hwT]
  obtain ⟨φ, hφ⟩ := Scheme.exists_comp_fromSpecStalk_eq (κ ≫ hW₀.fromSpec) (x := W.point) hκW
  refine ⟨U, (EtaleNeighborhood.isElementary_iff U).mpr hUres, φ, ?_, ?_⟩
  · refine (W.scheme.fromSpecStalk W.point).isEmbedding.injective ?_
    have h : W.scheme.fromSpecStalk W.point (φ cP) = W.point := by
      rw [← Scheme.Hom.comp_apply, hφ, hκW]
    rwa [Scheme.fromSpecStalk_closedPoint]
  · rw [reassoc_of% hφ]
    simpa only [g, Category.assoc] using hκ =≫ V.toBase

/-- **Replacing `S` by an elementary étale neighbourhood and by `Spec 𝒪_{S, s}` in turn.** If `V`
is an elementary étale neighbourhood of `(S, s)` and `W` is an elementary étale neighbourhood of
the closed point of `Spec 𝒪_{V, v}`, then there are a single elementary étale neighbourhood `U` of
`(S, s)` and a morphism `Spec 𝒪_{U, u} ⟶ Spec 𝒪_{W, w}` over `S` carrying the closed point to the
closed point. -/
theorem exists_isElementary_specStalkHom {S : Scheme.{u}} {s : S}
    (V : EtaleNeighborhood S s) (hV : V.IsElementary)
    (W : EtaleNeighborhood (Spec (V.scheme.presheaf.stalk V.point))
      (closedPoint (V.scheme.presheaf.stalk V.point))) (hW : W.IsElementary) :
    ∃ (U : EtaleNeighborhood S s) (_ : U.IsElementary)
      (φ : Spec (U.scheme.presheaf.stalk U.point) ⟶
            Spec (W.scheme.presheaf.stalk W.point)),
      φ (closedPoint (U.scheme.presheaf.stalk U.point)) =
          closedPoint (W.scheme.presheaf.stalk W.point) ∧
      φ ≫ W.scheme.fromSpecStalk W.point ≫ W.toBase ≫
            V.scheme.fromSpecStalk V.point ≫ V.toBase
          = U.scheme.fromSpecStalk U.point ≫ U.toBase :=
  exists_isElementary_specStalkHom_of_fromSpecStalk_eq V hV
    Scheme.fromSpecStalk_closedPoint W hW

end EtaleNeighborhood

end AlgebraicGeometry

end
