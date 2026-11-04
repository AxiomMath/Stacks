module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.FiniteCaseTrim
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Property (C) for an integral morphism which is a closed embedding

A morphism of schemes `f : X ⟶ Y` has *property (C)* when every scheme étale over `X` is
dominated, by a surjection over `X`, by the base change along `f` of a scheme étale over `Y`.
This file proves [Stacks, Tag 04DW]: an integral morphism which is a homeomorphism onto a closed
subset of its target has property (C).

## The shape of the argument

The conclusion is local on the étale scheme `g : U ⟶ X`, because a family of morphisms into `U`
whose images cover `U` can be assembled into a single surjection out of the coproduct of their
sources, and the base changes assemble into the base change of the coproduct of the bases
(`Stacks.EtaleCohomology.isPullback_pullbackFactorMap`). So it suffices to hit one point `u` of
`U` at a time.

Fix `u`. An étale morphism is locally quasi-finite
(`AlgebraicGeometry.locallyQuasiFinite_of_etale`), so its fibres are discrete and `u` is isolated
in its own fibre; shrinking `U` to an open neighbourhood of `u` on which the fibre of `g u` is
the single point `u` (`Stacks.EtaleCohomology.exists_opens_isolating_fiber`) makes `g` injective
on that fibre. Now `g` is an open map, so its image is open in `X`; since `f` is a homeomorphism
onto a closed subset, that image is carried to the intersection of `f '' X` with an open `T` of
`Y`. Taking `V = T` as an open subscheme of `Y`, the shrunk `U` maps to `X ×ₗᵧ V` by an étale
*surjection*, i.e. it is a one-member étale covering of `X ×ₗᵧ V`.

At this point property (B) for `f` — [Stacks, Tag 04DR], available here as
`Stacks.EtaleCohomology.hasPropertyB_of_isIntegralHom` — supplies an étale covering of `V` over
one member `V'` of which `X ×ₗᵧ V'` decomposes into pieces subordinate to the covering, that is,
mapping to the shrunk `U`. Descending the point `u` through that member gives a point of
`X ×ₗᵧ V'` over `u`, and the uniqueness in the fibre forces it to land on `u` itself.

## Main definitions

* `Stacks.EtaleCohomology.HasPropertyC` is property (C) for a morphism of schemes.

## Main results

* `Stacks.EtaleCohomology.hasPropertyC_of_isIntegralHom_of_isClosedEmbedding` is
  [Stacks, Tag 04DW]: an integral morphism of schemes which is a homeomorphism onto a closed
  subset of its target has property (C).

## Implementation notes

"A homeomorphism onto a closed subset" is `Topology.IsClosedEmbedding` on the underlying
continuous map. The commuting triangle in `Stacks.EtaleCohomology.HasPropertyC` records that the
dominating surjection is a morphism over `X`.

`Stacks.EtaleCohomology.pullbackFactorMap` carries the factorisation of one base morphism through
another as a hypothesis rather than in its type. That is what lets it be applied to the coproduct
inclusions `CategoryTheory.Limits.Sigma.ι`, for which the factorisation
`Sigma.ι V i ≫ Sigma.desc v = v i` holds only propositionally;
`Stacks.EtaleCohomology.pullbackBaseChangeMap`, which has the composite in its type, cannot be.

## References

* [Stacks Project, Tag 04DW](https://stacks.math.columbia.edu/tag/04DW)
* [Stacks Project, Tag 04DR](https://stacks.math.columbia.edu/tag/04DR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- Property (C) for a morphism of schemes `f : X ⟶ Y`: every scheme étale over `X` is dominated,
by a surjection of schemes over `X`, by the base change along `f` of a scheme étale over `Y`. -/
def HasPropertyC {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ {U : Scheme.{u}} (g : U ⟶ X), Etale g →
    ∃ (V : Scheme.{u}) (v : V ⟶ Y), Etale v ∧
      ∃ h : pullback f v ⟶ U, Surjective h ∧ h ≫ g = pullback.fst f v

/-! ### Fibre products over a factor of the base morphism -/

section Factor

variable {X Y : Scheme.{u}} {ι : Type u} [Small.{u} ι]
  (f : X ⟶ Y) (V : ι → Scheme.{u}) (vᵢ : ∀ i, V i ⟶ Y) (v : (∐ V) ⟶ Y)
  (hv : ∀ i, Sigma.ι V i ≫ v = vᵢ i) (i : ι)

/-- The comparison morphism from the fibre product of `f` with one factor `vᵢ i` of the base
morphism `v` to the fibre product of `f` with `v` itself, given a factorisation of `vᵢ i` through
`v` along the coproduct inclusion. -/
private noncomputable def pullbackFactorMap : pullback f (vᵢ i) ⟶ pullback f v :=
  pullback.map f (vᵢ i) f v (𝟙 X) (Sigma.ι V i) (𝟙 Y) (by simp) (by simpa using (hv i).symm)

/-- The comparison morphism of a factor commutes with the projection to `X`. -/
private lemma pullbackFactorMap_fst :
    pullbackFactorMap f V vᵢ v hv i ≫ pullback.fst f v = pullback.fst f (vᵢ i) := by
  show pullback.lift (pullback.fst f (vᵢ i)) (pullback.snd f (vᵢ i) ≫ Sigma.ι V i) _ ≫ _ = _
  exact pullback.lift_fst _ _ _

/-- The comparison morphism of a factor carries the projection to the coproduct to the projection
to the factor followed by the coproduct inclusion. -/
private lemma pullbackFactorMap_snd :
    pullbackFactorMap f V vᵢ v hv i ≫ pullback.snd f v =
      pullback.snd f (vᵢ i) ≫ Sigma.ι V i := by
  show pullback.lift (pullback.fst f (vᵢ i)) (pullback.snd f (vᵢ i) ≫ Sigma.ι V i) _ ≫ _ = _
  exact pullback.lift_snd _ _ _

/-- The morphism out of a cone over `pullback.snd f v` and `Sigma.ι V i` witnessing that the
square of `Stacks.EtaleCohomology.isPullback_pullbackFactorMap` is cartesian. -/
private noncomputable def pullbackFactorLift
    (s : PullbackCone (pullback.snd f v) (Sigma.ι V i)) : s.pt ⟶ pullback f (vᵢ i) :=
  pullback.lift (s.fst ≫ pullback.fst f v) s.snd (by
    rw [Category.assoc, pullback.condition, reassoc_of% s.condition, hv])

/-- The cone morphism of `Stacks.EtaleCohomology.pullbackFactorLift` on the projection to `X`. -/
private lemma pullbackFactorLift_fst
    (s : PullbackCone (pullback.snd f v) (Sigma.ι V i)) :
    pullbackFactorLift f V vᵢ v hv i s ≫ pullback.fst f (vᵢ i) = s.fst ≫ pullback.fst f v := by
  unfold pullbackFactorLift
  exact pullback.lift_fst _ _ _

/-- The cone morphism of `Stacks.EtaleCohomology.pullbackFactorLift` on the projection to the
factor. -/
private lemma pullbackFactorLift_snd
    (s : PullbackCone (pullback.snd f v) (Sigma.ι V i)) :
    pullbackFactorLift f V vᵢ v hv i s ≫ pullback.snd f (vᵢ i) = s.snd := by
  unfold pullbackFactorLift
  exact pullback.lift_snd _ _ _

/-- **The fibre product over a factor is a fibre product.** The comparison morphism of a factor,
together with the projection to that factor, exhibits `X ×ₗᵧ V i` as the fibre product of
`X ×ₗᵧ (∐ V) ⟶ ∐ V` with the coproduct inclusion of `V i`. -/
private lemma isPullback_pullbackFactorMap :
    IsPullback (pullbackFactorMap f V vᵢ v hv i) (pullback.snd f (vᵢ i))
      (pullback.snd f v) (Sigma.ι V i) := by
  let c : PullbackCone (pullback.snd f v) (Sigma.ι V i) :=
    PullbackCone.mk (pullbackFactorMap f V vᵢ v hv i) (pullback.snd f (vᵢ i))
      (pullbackFactorMap_snd f V vᵢ v hv i)
  apply IsPullback.of_isLimit (c := c)
  refine PullbackCone.IsLimit.mk (pullbackFactorMap_snd f V vᵢ v hv i)
    (pullbackFactorLift f V vᵢ v hv i) ?_ ?_ ?_
  · intro s
    apply pullback.hom_ext
    · rw [Category.assoc, pullbackFactorMap_fst, pullbackFactorLift_fst]
    · rw [Category.assoc, pullbackFactorMap_snd, ← Category.assoc, pullbackFactorLift_snd,
        s.condition]
  · exact pullbackFactorLift_snd f V vᵢ v hv i
  · intro s m h₁ h₂
    apply pullback.hom_ext
    · rw [pullbackFactorLift_fst, ← h₁, Category.assoc, pullbackFactorMap_fst]
    · rw [h₂, pullbackFactorLift_snd]

/-- **The factors cut out open pieces.** Since the coproduct inclusions are open immersions and
open immersions are stable under base change, the comparison morphism of a factor is an open
immersion. -/
private lemma isOpenImmersion_pullbackFactorMap [IsOpenImmersion (Sigma.ι V i)] :
    IsOpenImmersion (pullbackFactorMap f V vᵢ v hv i) := by
  rw [← (isPullback_pullbackFactorMap f V vᵢ v hv i).isoPullback_hom_fst]
  infer_instance

end Factor

/-! ### Isolating a point in its fibre -/

/-- **An isolated point of a fibre has a neighbourhood meeting that fibre only in it.** For a
locally quasi-finite morphism `g : U ⟶ X` and a point `u` of `U` there is an open neighbourhood
of `u` in `U` on which `g` takes the value `g u` only at `u`.

Local quasi-finiteness enters through the discreteness of the fibres of `g`. -/
@[sga "3 V 7.3" "partial"]
private lemma exists_opens_isolating_fiber {U X : Scheme.{u}} (g : U ⟶ X)
    [LocallyQuasiFinite g] (u : U) :
    ∃ W : U.Opens, u ∈ W.1 ∧ ∀ z ∈ W.1, g z = g u → z = u := by
  have hiso : IsOpen ({g.asFiber u} : Set (g.fiber (g u))) := isOpen_discrete _
  let e := g.fiberHomeo (g u)
  let F : Set U := g ⁻¹' {g u}
  let pt : F := ⟨u, rfl⟩
  have hsub : IsOpen ({pt} : Set F) := by
    have himage : e '' ({g.asFiber u} : Set (g.fiber (g u))) = {pt} := by
      rw [Set.image_singleton]
      congr 1
      apply Subtype.ext
      simp [e, pt]
    rw [← himage]
    exact e.isOpen_image.mpr hiso
  obtain ⟨W, hW, hWpre⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hsub
  refine ⟨⟨W, hW⟩, ?_, ?_⟩
  · show pt ∈ Subtype.val ⁻¹' W
    rw [hWpre]
    exact Set.mem_singleton pt
  · intro z hz hzg
    have hz' : (⟨z, hzg⟩ : F) ∈ Subtype.val ⁻¹' W := hz
    rw [hWpre] at hz'
    exact congrArg Subtype.val (Set.mem_singleton_iff.mp hz')

/-! ### Property (C) one point at a time -/

/-- **Property (C) at a single point.** Let `f : X ⟶ Y` be integral and a homeomorphism onto a
closed subset, let `g : U ⟶ X` be étale and let `u` be a point of `U`. There is a scheme `V`
étale over `Y` and a morphism `X ×ₗᵧ V ⟶ U` over `X` whose image contains `u`.

This is the whole mathematical content of [Stacks, Tag 04DW]; property (B) for `f`,
[Stacks, Tag 04DR], is the input. -/
private lemma exists_etale_dominating_at_point
    {X Y U : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]
    (hf : Topology.IsClosedEmbedding f) (g : U ⟶ X) [Etale g] (u : U) :
    ∃ (V : Scheme.{u}) (v : V ⟶ Y), Etale v ∧
      ∃ h : pullback f v ⟶ U, h ≫ g = pullback.fst f v ∧ ∃ z, h z = u := by
  let _ : LocallyQuasiFinite g := (locallyQuasiFinite_of_etale g).2
  obtain ⟨W, huW, hsingle⟩ := exists_opens_isolating_fiber g u
  let U' := U.restrict W.isOpenEmbedding
  let inc : U' ⟶ U := U.ofRestrict W.isOpenEmbedding
  let g' : U' ⟶ X := inc ≫ g
  let hu' : U' := ⟨u, huW⟩
  have huniq : ∀ z : U', g' z = g' hu' → z = hu' := by
    intro z hz
    exact Subtype.ext (hsingle z.1 z.2 hz)
  have hRange : IsOpen (Set.range g'.base) := g'.isOpenMap.isOpen_range
  obtain ⟨Tset, hTset, himage⟩ := hf.isInducing.image_eq_isOpen_inter_range hRange
  let T : Y.Opens := ⟨Tset, hTset⟩
  let V : Scheme.{u} := Y.restrict T.isOpenEmbedding
  let v : V ⟶ Y := Y.ofRestrict T.isOpenEmbedding
  have hyT (z : U') : f (g' z) ∈ Tset := by
    have hz : f (g' z) ∈ f.base '' Set.range g'.base := ⟨g' z, ⟨z, rfl⟩, rfl⟩
    rw [himage] at hz
    exact hz.1
  have hmap : Set.range (g' ≫ f).base ⊆ Set.range v.base := by
    intro y hy
    obtain ⟨z, rfl⟩ := hy
    refine ⟨⟨f (g' z), hyT z⟩, ?_⟩
    show (TopologicalSpace.Opens.inclusion' T) ⟨f (g' z), hyT z⟩ = f (g' z)
    rfl
  let w : U' ⟶ V := IsOpenImmersion.lift v (g' ≫ f) hmap
  have hw : w ≫ v = g' ≫ f := IsOpenImmersion.lift_fac v (g' ≫ f) hmap
  let m : U' ⟶ pullback f v := pullback.lift g' w (by rw [hw])
  have hmcomp : m ≫ pullback.fst f v = g' := by
    simpa [m] using (pullback.lift_fst g' w (by rw [hw]))
  have hmEtale : Etale m := by
    let _ : Etale (m ≫ pullback.fst f v) := by rw [hmcomp]; infer_instance
    exact Etale.of_comp (f := m) (g := pullback.fst f v)
  have hmSurj : Function.Surjective m := by
    intro p
    let x := pullback.fst f v p
    let y := pullback.snd f v p
    have hxy : f x = v y := by
      have hp := congrArg (fun k : pullback f v ⟶ Y => k p) pullback.condition
      simpa [x, y] using hp
    have hyT : v y ∈ Tset := y.2
    have hximage : f x ∈ f.base '' Set.range g'.base := by
      rw [himage]
      exact ⟨by simpa [hxy] using hyT, ⟨x, rfl⟩⟩
    obtain ⟨_, ⟨z', hz'⟩, hfx⟩ := hximage
    have hx : g' z' = x := hf.injective ((congrArg f hz').trans hfx)
    refine ⟨z', ?_⟩
    apply (pullback.fst f v).isOpenEmbedding.injective
    show (m ≫ pullback.fst f v) z' = pullback.fst f v p
    rw [hmcomp]
    exact hx
  let 𝒰 : (pullback f v).Cover.{u} Scheme.etalePrecoverage :=
    { I₀ := PUnit.{u + 1}
      X := fun _ => U'
      f := fun _ => m
      mem₀ := by
        show Presieve.ofArrows (fun _ : PUnit.{u + 1} => U') (fun _ => m) ∈
          Scheme.etalePrecoverage (pullback f v)
        rw [Presieve.ofArrows_pUnit]
        exact (Scheme.singleton_mem_precoverage_iff (P := @Etale) m).2 ⟨hmSurj, hmEtale⟩ }
  obtain ⟨𝒱, h𝒱⟩ := hasPropertyB_of_isIntegralHom f (V := V) v 𝒰
  let _ : Scheme.IsJointlySurjectivePreserving (@Etale : MorphismProperty Scheme.{u}) :=
    Scheme.isJointlySurjectivePreserving @Etale
  let _ : Scheme.JointlySurjective Scheme.etalePrecoverage := by
    show Scheme.JointlySurjective (Scheme.precoverage @Etale)
    refine ⟨?_⟩
    intro Z R hR x
    rcases hR with ⟨hR, hEt⟩
    rw [Scheme.jointlySurjectivePrecoverage,
      Presieve.mem_comap_jointlySurjectivePrecoverage_iff] at hR
    obtain ⟨Z', k, hk, hx⟩ := hR x
    exact ⟨Z', k, hk, hx⟩
  let y : V := ⟨f (g' hu'), hyT hu'⟩
  obtain ⟨j, yj, hyj⟩ := 𝒱.exists_eq y
  obtain ⟨q, hq₁, _, Wj, e, a, ha⟩ := h𝒱 j
  let hj : pullback f (𝒱.f j ≫ v) ⟶ U' := e.inv ≫ Sigma.desc a
  have hsum : Sigma.desc a ≫ g' = e.hom ≫ q ≫ pullback.fst f v := by
    apply Sigma.hom_ext
    intro i
    have hfi : 𝒰.f i = m := by cases i; rfl
    have hid : Sigma.ι Wj i ≫ Sigma.desc a = a i := Sigma.ι_desc a i
    calc
      Sigma.ι Wj i ≫ Sigma.desc a ≫ g' = (Sigma.ι Wj i ≫ Sigma.desc a) ≫ g' :=
        (Category.assoc _ _ _).symm
      _ = a i ≫ g' := by rw [hid]; rfl
      _ = a i ≫ (m ≫ pullback.fst f v) := by rw [hmcomp]
      _ = (a i ≫ m) ≫ pullback.fst f v := (Category.assoc _ _ _).symm
      _ = (a i ≫ 𝒰.f i) ≫ pullback.fst f v := by rw [hfi]
      _ = (Sigma.ι Wj i ≫ e.hom ≫ q) ≫ pullback.fst f v := by rw [ha i]
      _ = Sigma.ι Wj i ≫ e.hom ≫ q ≫ pullback.fst f v := by simp
  have hjbase : hj ≫ g' = pullback.fst f (𝒱.f j ≫ v) := by
    calc
      hj ≫ g' = e.inv ≫ (Sigma.desc a ≫ g') := Category.assoc _ _ _
      _ = e.inv ≫ (e.hom ≫ q ≫ pullback.fst f v) := by rw [hsum]
      _ = q ≫ pullback.fst f v := by simp
      _ = pullback.fst f (𝒱.f j ≫ v) := hq₁
  let vj := 𝒱.f j ≫ v
  let _ : Etale (𝒱.f j) := 𝒱.map_prop j
  have hvj : Etale vj := inferInstance
  let y' : 𝒱.X j := yj
  have hxy' : f (g' hu') = vj y' := by
    calc
      f (g' hu') = v y := rfl
      _ = v (𝒱.f j yj) := by rw [← hyj]
      _ = vj y' := rfl
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (g' hu') y' hxy'
  refine ⟨𝒱.X j, vj, hvj, hj ≫ inc, ?_, ?_⟩
  · rw [Category.assoc, hjbase]
  · refine ⟨z, ?_⟩
    have hpoint : g' (hj z) = g' hu' := by
      calc
        g' (hj z) = (hj ≫ g') z := by simp
        _ = (pullback.fst f vj) z := by rw [hjbase]
        _ = g' hu' := hz₁
    calc
      (hj ≫ inc) z = inc (hj z) := by simp
      _ = inc hu' := congrArg inc (huniq (hj z) hpoint)
      _ = u := rfl

/-! ### Property (C) -/

/-- **Stacks Project, Tag 04DW.** An integral morphism of schemes which is a homeomorphism onto a
closed subset of its target has property (C): every scheme étale over the source is dominated, by
a surjection over the source, by the base change of a scheme étale over the target.

The étale scheme over the target is the coproduct of the one-point constructions of
`Stacks.EtaleCohomology.exists_etale_dominating_at_point`, indexed by the points of the given
étale scheme; its base change is the coproduct of their base changes by
`Stacks.EtaleCohomology.isPullback_pullbackFactorMap`, so the one-point morphisms assemble into a
single morphism, and it is surjective because every point was hit. -/
@[stacks 04DW]
theorem hasPropertyC_of_isIntegralHom_of_isClosedEmbedding
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] (hf : Topology.IsClosedEmbedding f) :
    HasPropertyC f := by
  intro U g _
  choose V v hv h hh z hz using fun x : U => exists_etale_dominating_at_point f hf g x
  let vbig : (∐ V) ⟶ Y := Sigma.desc v
  have hvbig (i : U) : Sigma.ι V i ≫ vbig = v i := Sigma.ι_desc v i
  let q (i : U) : pullback f (v i) ⟶ pullback f vbig :=
    pullbackFactorMap f V v vbig hvbig i
  have hqfst (i : U) : q i ≫ pullback.fst f vbig = pullback.fst f (v i) :=
    pullbackFactorMap_fst f V v vbig hvbig i
  have hqsnd (i : U) : q i ≫ pullback.snd f vbig = pullback.snd f (v i) ≫ Sigma.ι V i :=
    pullbackFactorMap_snd f V v vbig hvbig i
  have hqoi (i : U) : IsOpenImmersion (q i) := by
    dsimp only [q]
    exact isOpenImmersion_pullbackFactorMap f V v vbig hvbig i
  have hcover : ⨆ i : U, (q i).opensRange = ⊤ := by
    rw [eq_top_iff]
    intro p hp
    let w := (sigmaMk V).symm ((pullback.snd f vbig) p)
    have hw : Sigma.ι V w.1 w.2 = (pullback.snd f vbig) p := by
      calc
        Sigma.ι V w.1 w.2 = sigmaMk V ⟨w.1, w.2⟩ := (sigmaMk_mk V w.1 w.2).symm
        _ = (pullback.snd f vbig) p := by
          dsimp only [w]
          exact (sigmaMk V).apply_symm_apply ((pullback.snd f vbig) p)
    obtain ⟨r, hr₁, hr₂⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := pullback.snd f vbig) (g := Sigma.ι V w.1) p w.2 hw.symm
    let k := isPullback_pullbackFactorMap f V v vbig hvbig w.1
    have hp' : q w.1 (k.isoPullback.inv r) = p := by
      show (k.isoPullback.inv ≫ q w.1) r = p
      rw [k.isoPullback_inv_fst]
      exact hr₁
    exact (TopologicalSpace.Opens.mem_iSup).2 ⟨w.1, ⟨k.isoPullback.inv r, hp'⟩⟩
  have hsnd (k : U) (x : ↑(pullback f (v k))) :
      pullback.snd f vbig (q k x) = Sigma.ι V k (pullback.snd f (v k) x) :=
    congrArg (fun φ => φ x) (hqsnd k)
  have hdisj : Pairwise (fun i j : U => Disjoint (q i).opensRange (q j).opensRange) := by
    intro i j hij
    rw [disjoint_iff, TopologicalSpace.Opens.ext_iff]
    ext p
    constructor
    · rintro ⟨hp_i, hp_j⟩
      change p ∈ Set.range (q i) at hp_i
      change p ∈ Set.range (q j) at hp_j
      rcases hp_i with ⟨x, hx⟩
      rcases hp_j with ⟨y, hy⟩
      have heq : q i x = q j y := hx.trans hy.symm
      have hV : Sigma.ι V i ((pullback.snd f (v i)) x) =
          Sigma.ι V j ((pullback.snd f (v j)) y) :=
        (hsnd i x).symm.trans ((congrArg _ heq).trans (hsnd j y))
      have hindex : Sigma.mk (β := fun i : U => V i) i ((pullback.snd f (v i)) x) =
          Sigma.mk (β := fun i : U => V i) j ((pullback.snd f (v j)) y) := by
        apply (sigmaMk V).injective
        simpa only [sigmaMk_mk] using hV
      exact hij (congrArg Sigma.fst hindex)
    · intro hfalse
      exact False.elim hfalse
  let _ : ∀ i : U, IsOpenImmersion (q i) := hqoi
  have hcol : Nonempty (IsColimit (Cofan.mk (pullback f vbig) q)) :=
    nonempty_isColimit_cofanMk_of q hcover hdisj
  have : IsIso (Sigma.desc q) :=
    (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk (pullback f vbig) q)).mp hcol
  let e : (∐ fun i : U => pullback f (v i)) ≅ pullback f vbig := asIso (Sigma.desc q)
  let hbig : pullback f vbig ⟶ U := e.inv ≫ Sigma.desc h
  have hsum : Sigma.desc h ≫ g = Sigma.desc q ≫ pullback.fst f vbig := by
    apply Sigma.hom_ext
    intro i
    simp [hh, hqfst]
  have hcomp : hbig ≫ g = pullback.fst f vbig := by
    simp only [hbig, Category.assoc, hsum]
    exact e.inv_hom_id_assoc _
  have hecomp : e.hom ≫ hbig = Sigma.desc h := by simp [hbig, e]
  have hsurj : Function.Surjective hbig := by
    intro x
    refine ⟨e.hom (Sigma.ι (fun i : U => pullback f (v i)) x (z x)), ?_⟩
    show (Sigma.ι (fun i : U => pullback f (v i)) x ≫ e.hom ≫ hbig) (z x) = x
    rw [hecomp, Sigma.ι_desc]
    exact hz x
  have hvbig_etale : Etale vbig :=
    have : IsZariskiLocalAtSource (@Etale : MorphismProperty Scheme.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale)
    IsZariskiLocalAtSource.sigmaDesc hv
  exact ⟨∐ V, vbig, hvbig_etale, hbig, ⟨hsurj⟩, hcomp⟩

end Stacks.EtaleCohomology

end
