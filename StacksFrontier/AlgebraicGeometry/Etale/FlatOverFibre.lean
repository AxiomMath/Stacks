module

public import StacksFrontier.AlgebraicGeometry.Descent.Modules.FpqcFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.FlatFinitePresentation05I5
public import StacksFrontier.AlgebraicGeometry.Etale.FlatFiniteTypeModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleStalk.ElementaryFiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme

/-!
# Flatness and finite presentation over a whole fibre after an elementary étale neighbourhood

Let `f : X ⟶ S` be of finite presentation, let `F` be a quasi-coherent `𝒪_X`-module of finite
type, and let `s` be a point of `S` at every point of whose fibre `X_s` the module `F` is flat
over `S`. Then after an elementary étale neighbourhood `(S', s')` of `(S, s)` there is an open
`V ⊆ X ×_S Spec 𝒪_{S', s'}` containing the *whole* fibre `X_s = X ×_S s'` on which the pullback
of `F` is of finite presentation and flat over `𝒪_{S', s'}`. This is Stacks 05KU, the uniform
version of Stacks 05I5, which gives the same conclusion near a single point of `X_s`.

The proof follows the source. Stacks 05I5 at a point `x` of `X_s` produces a neighbourhood
`(S_x, s_x)` and an open `V_x`; since `(S_x, s_x)` is elementary the fibre of
`X ×_S Spec 𝒪_{S_x, s_x} ⟶ Spec 𝒪_{S_x, s_x}` over the point lying over `s_x` is `X_s` itself,
so `V_x` already contains the point over every point of an open neighbourhood of `x` in `X_s`.
The fibre `X_s` is quasi-compact, so finitely many such neighbourhoods cover it; the category of
elementary étale neighbourhoods of `(S, s)` is cofiltered (Stacks 057B), so one `(S', s')`
dominates all the finitely many `(S_{x_i}, s_{x_i})`, and the open `V` is the union of the
inverse images of the `V_{x_i}` in `X ×_S Spec 𝒪_{S', s'}`.

Only the finite-presentation clause has to be transported to that union: finite presentation is
preserved by pullback (Stacks 01BQ) and is local on an fpqc — in particular on an open — covering
(Stacks 05B0). Flatness is then free, exactly as in Stacks 05I5: the locus inside `V` where the
pullback of `F` is flat over `𝒪_{S', s'}` is open because the pullback is of finite presentation
there (Stacks 0399), and it contains the whole fibre because `F` is flat over `S` at every point
of `X_s` and flatness over the base at a point is preserved by base change (Stacks 01U8).

## Main results

* `AlgebraicGeometry.exists_hom_specStalk_of_apply_eq` is the functoriality of `Spec` of the
  local ring: a morphism carrying `x` to `y` induces a morphism
  `Spec 𝒪_{X, x} ⟶ Spec 𝒪_{Y, y}` compatible with the canonical morphisms to `X` and `Y`.
* `AlgebraicGeometry.exists_isOpen_nhds_fiber_forall_mem` says that an open of a base change
  which is trivial on the residue field at the point below `s` and has at most one point above
  each point of `X_s` contains, once it contains the point above one point of `X_s`, the point
  above every point of an open neighbourhood in `X_s`.
* `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_isFinitePresentation_nhds` is Stacks 05I5
  read uniformly over a neighbourhood in the fibre, keeping the finite-presentation clause.
* `AlgebraicGeometry.exists_open_isFinitePresentation_isFlatOver_of_subset` shrinks an open of a
  base change on which the pullback of `F` is of finite presentation to one on which it is also
  flat over the new base, keeping every point at which `F` is flat over `S`.
* `AlgebraicGeometry.exists_hom_pullback_isFinitePresentation_preimage` carries an open with
  finitely presented pullback along a morphism of bases over `S`.
* `AlgebraicGeometry.isFinitePresentation_pullback_ι_iSup` assembles finite presentation of the
  pullback of a quasi-coherent module to a union of opens out of its pieces.
* `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_isFinitePresentation_isFlatOver_fiber`
  is **Stacks 05KU**.

## Implementation notes

The vocabulary of the fibre is the one of
`StacksFrontier/AlgebraicGeometry/Etale/FlatFiniteTypeModules.lean`: the fibre is the
scheme-theoretic fibre `AlgebraicGeometry.Scheme.Hom.fiber`, a point of `X` lying over `s` is a
point `x` with `f x = s`, and the identification of `X_s` with the fibre of a base change which
is trivial on residue fields is `AlgebraicGeometry.exists_homeomorph_fiber`.

The conclusion states that `V` contains every point of `X ×_S Spec 𝒪_{S', s'}` whose image in
`X` lies over `s`. That set is exactly the fibre `X ×_S s'` of the source: the fibre of
`Spec 𝒪_{S', s'} ⟶ S` over `s` is the single point lying over `s'`.

The dominating neighbourhood is produced in the category
`AlgebraicGeometry.ElementaryEtaleNeighborhood S s`, whose objects are elementary étale
neighbourhoods and which is cofiltered; the finitely many neighbourhoods to be dominated are
collected as a `Finset` of its objects.

## References

* [Stacks Project, Tag 05KU](https://stacks.math.columbia.edu/tag/05KU)
* [Stacks Project, Tag 05I5](https://stacks.math.columbia.edu/tag/05I5)
* [Stacks Project, Tag 057B](https://stacks.math.columbia.edu/tag/057B)
* [Stacks Project, Tag 05B0](https://stacks.math.columbia.edu/tag/05B0)
* [Stacks Project, Tag 01BQ](https://stacks.math.columbia.edu/tag/01BQ)
* [Stacks Project, Tag 01U8](https://stacks.math.columbia.edu/tag/01U8)
* [Stacks Project, Tag 0399](https://stacks.math.columbia.edu/tag/0399)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

/-- **Functoriality of the local scheme at a point.** A morphism of schemes `g : X ⟶ Y` carrying
`x` to `y` induces a morphism `Spec 𝒪_{X, x} ⟶ Spec 𝒪_{Y, y}` commuting with the canonical
morphisms `Spec 𝒪_{X, x} ⟶ X` and `Spec 𝒪_{Y, y} ⟶ Y`.

Stated for the existence of the morphism, with the target point given as a variable, so that no
transport along `g x = y` appears in the conclusion. -/
theorem exists_hom_specStalk_of_apply_eq {X Y : Scheme.{u}} (g : X ⟶ Y) (x : X) (y : Y)
    (hxy : g x = y) :
    ∃ c : Spec (X.presheaf.stalk x) ⟶ Spec (Y.presheaf.stalk y),
      c ≫ Y.fromSpecStalk y = X.fromSpecStalk x ≫ g := by
  subst hxy
  exact ⟨Spec.map (g.stalkMap x), Scheme.SpecMap_stalkMap_fromSpecStalk g⟩

/-- **An open of a base change captures a neighbourhood in the fibre.** Let `b : T ⟶ S` carry a
point `y` to `s` and induce an isomorphism `κ(s) ⟶ κ(y)`, and assume that `X ×_S T` has at most
one point above each point of `X` lying over `s`. If an open `V` of `X ×_S T` contains the point
above a point `f.fiberι s w` of the fibre `X_s`, then it contains the point above
`f.fiberι s w'` for every `w'` in an open neighbourhood of `w` in `X_s`.

The residue field condition identifies the fibre of `X ×_S T ⟶ T` over `y` with `X_s`, by
`AlgebraicGeometry.exists_homeomorph_fiber`; the neighbourhood is the inverse image of `V` under
that identification. For an elementary étale neighbourhood `(U, u)` of `(S, s)` and
`b : Spec 𝒪_{U, u} ⟶ S` both hypotheses hold, the second by
`AlgebraicGeometry.eq_of_pullback_fst_eq`. -/
theorem exists_isOpen_nhds_fiber_forall_mem {X S T : Scheme.{u}} (f : X ⟶ S) (b : T ⟶ S)
    {s : S} {y : T} (hby : b y = s) (hres : IsIso (b.residueFieldMap y))
    (huniq : ∀ (x : X) (p q : ↑(pullback f b)), f x = s → pullback.fst f b p = x →
      pullback.fst f b q = x → p = q)
    (w : f.fiber s) (V : (pullback f b).Opens)
    (hw : ∃ v : V, pullback.fst f b ⁻¹' {f.fiberι s w} = {V.ι v}) :
    ∃ W : Set (f.fiber s), IsOpen W ∧ w ∈ W ∧
      ∀ w' ∈ W, ∀ p : ↑(pullback f b),
        pullback.fst f b p = f.fiberι s w' → p ∈ V := by
  obtain ⟨e, he⟩ := exists_homeomorph_fiber f b hby hres
  obtain ⟨v, hv⟩ := hw
  refine ⟨{z | (pullback.snd f b).fiberι y (e z) ∈ V}, V.2.preimage
    (((pullback.snd f b).fiberι y).continuous.comp e.continuous), ?_, ?_⟩
  · have hmem : (pullback.snd f b).fiberι y (e w) ∈ ({V.ι v} : Set ↑(pullback f b)) := by
      rw [← hv]
      exact he w
    show (pullback.snd f b).fiberι y (e w) ∈ V.1
    rw [Set.eq_of_mem_singleton hmem]
    exact v.2
  · intro w' hw' p hp
    rw [huniq (f.fiberι s w') p _ (f.apply_fiberι s w') hp (he w')]
    exact hw'

/-- **Stacks Project, Tag 05I5 at a point of a fibre, uniformly over a neighbourhood in the
fibre.** At a point `w` of `X_s` at which `F` is flat over `S` there is an elementary étale
neighbourhood `(S', s')` of `(S, s)` and an open `V ⊆ X ×_S Spec 𝒪_{S', s'}` on which the
pullback of `F` is of finite presentation and which contains the point over `f.fiberι s w'` for
every `w'` in an open neighbourhood of `w` in `X_s`.

This is `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_isFlatOverAt_nhds` with the
flatness clause of Tag 05I5 traded for its finite-presentation clause, which is the half that
the proof of Tag 05KU has to transport to a union. -/
theorem exists_elementaryEtaleNeighborhood_isFinitePresentation_nhds {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] {s : S} (w : f.fiber s)
    (hw : IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s w)) :
    ∃ (U : EtaleNeighborhood S s) (_ : U.IsElementary) (W : Set (f.fiber s)),
      IsOpen W ∧ w ∈ W ∧
      ∃ V : (pullback f (U.scheme.fromSpecStalk U.point ≫ U.toBase)).Opens,
        ((Scheme.Modules.pullback (V.ι ≫ pullback.fst f
          (U.scheme.fromSpecStalk U.point ≫ U.toBase))).obj F).IsFinitePresentation ∧
        ∀ w' ∈ W, ∀ p : ↑(pullback f (U.scheme.fromSpecStalk U.point ≫ U.toBase)),
          pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase) p = f.fiberι s w' →
            p ∈ V := by
  have hfa : f (f.fiberι s w) = s := f.apply_fiberι s w
  obtain ⟨U₀, hU₀, V, v, huniq, hfp, -⟩ :=
    (show ExistsElementaryEtaleNeighborhoodFinitePresentationFlatOver.{u} from
          @existsElementaryEtaleNeighborhoodFinitePresentationFlatOver.{u}) f F (f.fiberι s w) hw
  set U : EtaleNeighborhood S s := U₀.congrPoint hfa
  have hU : U.IsElementary := hU₀.congrPoint hfa
  obtain ⟨y, hy⟩ := exists_fromSpecStalk_eq U.point
  have hby : (U.scheme.fromSpecStalk U.point ≫ U.toBase) y = s := by
    rw [Scheme.Hom.comp_apply, hy, U.map_point]
  have hres : IsIso ((U.scheme.fromSpecStalk U.point ≫ U.toBase).residueFieldMap y) :=
    isIso_residueFieldMap_fromSpecStalk_comp U.toBase U.point
      ((EtaleNeighborhood.isElementary_iff U).mp hU) hy
  obtain ⟨W, hWo, hwW, hWsub⟩ :=
    exists_isOpen_nhds_fiber_forall_mem f (U.scheme.fromSpecStalk U.point ≫ U.toBase) hby hres
      (fun x p q hx hp hq => eq_of_pullback_fst_eq f U hU hx hp hq) w V ⟨v, huniq⟩
  exact ⟨U, hU, W, hWo, hwW, V, hfp, hWsub⟩

/-- Finite presentation of the pullback of a module along `g` passes to `i ≫ g`. -/
private theorem isFinitePresentation_pullback_comp {X Y Z : Scheme.{u}} (i : Y ⟶ Z) (g : Z ⟶ X)
    (F : X.Modules) (h : ((Scheme.Modules.pullback g).obj F).IsFinitePresentation) :
    ((Scheme.Modules.pullback (i ≫ g)).obj F).IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation Y.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.pullbackComp i g).app F)
    (@Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _ i.toLRSHom.toShHom _ h)

/-- **Shrinking to the flat locus, keeping a prescribed set of points.** The square
`IsPullback p q f b` presents `P` as a base change of `f : X ⟶ S` along `b : T ⟶ S`. Let `W` be
an open of `P` on which the pullback of a quasi-coherent `F` along `W ⟶ X` is of finite
presentation, and let `A ⊆ W` be a set of points at whose images in `X` the module `F` is flat
over `S`. Then `W` contains an open `V ⊇ A` on which the pullback of `F` is of finite
presentation *and* flat over `T`.

The locus in `W` where the pullback is flat over `T` is open by Tag 0399, and it contains `A` by
base change of flatness over the base at a point, Tag 01U8. -/
theorem exists_open_isFinitePresentation_isFlatOver_of_subset
    {X S T P : Scheme.{u}} {f : X ⟶ S} {b : T ⟶ S} {p : P ⟶ X} {q : P ⟶ T}
    [LocallyOfFinitePresentation f] (hpb : IsPullback p q f b)
    (F : X.Modules) [hFqc : F.IsQuasicoherent] (W : P.Opens)
    (hWfp : ((Scheme.Modules.pullback (W.ι ≫ p)).obj F).IsFinitePresentation)
    (A : Set P) (hAW : A ⊆ W.1)
    (hA : ∀ z ∈ A, IsFlatOverAt f.toLRSHom.toShHom F (p z)) :
    ∃ V : P.Opens, A ⊆ V.1 ∧ V ≤ W ∧
      ((Scheme.Modules.pullback (V.ι ≫ p)).obj F).IsFinitePresentation ∧
      IsFlatOver (V.ι ≫ q).toLRSHom.toShHom ((Scheme.Modules.pullback (V.ι ≫ p)).obj F) := by
  classical
  set G : W.toScheme.Modules := (Scheme.Modules.pullback (W.ι ≫ p)).obj F with hG
  have hGqc : G.IsQuasicoherent := by
    obtain ⟨σ, -⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData G (self := hWfp)
    exact σ.isQuasicoherent
  have hq : LocallyOfFinitePresentation q :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hpb inferInstance
  have hWq : LocallyOfFinitePresentation (W.ι ≫ q) :=
    MorphismProperty.comp_mem @LocallyOfFinitePresentation _ _ inferInstance hq
  set Ω : W.toScheme.Opens :=
    ⟨{t : W.toScheme | IsFlatOverAt (W.ι ≫ q).toLRSHom.toShHom G t},
      isOpen_setOf_flatOverAt (W.ι ≫ q) G⟩
  -- every point of `W` over a point where `F` is flat over `S` lies in the flat locus
  have : SheafOfModules.IsQuasicoherent (R := structureSheafRing X.toRingedSpace) F := hFqc
  have hmemΩ' : ∀ t : W.toScheme, IsFlatOverAt f.toLRSHom.toShHom F (p (W.ι t)) → t ∈ Ω := by
    intro t ht
    have hbase : IsFlatOverAt q.toLRSHom.toShHom ((modulePullback p.toLRSHom.toShHom).obj F)
        (W.ι t) := modulePullback_isFlatOverAt hpb F (W.ι t) ht
    have hcomp : IsFlatOverAt (W.ι ≫ q).toLRSHom.toShHom
        ((Scheme.Modules.pullback W.ι).obj ((Scheme.Modules.pullback p).obj F)) t :=
      (isFlatOverAt_iff_modulePullback_isFlatOverAt W.ι q _ t (Flat.stalkMap W.ι t)).mp hbase
    show IsFlatOverAt (W.ι ≫ q).toLRSHom.toShHom G t
    rw [hG]
    exact (isFlatOverAt_iff_of_moduleIso (W.ι ≫ q).toLRSHom.toShHom
      ((Scheme.Modules.pullbackComp W.ι p).app F) t).mp hcomp
  set V : P.Opens := W.ι ''ᵁ Ω with hV
  have hVW : V ≤ W := Scheme.Opens.ι_image_le W Ω
  set i : V.toScheme ⟶ W.toScheme := P.homOfLE hVW with hi
  have hiι : i ≫ W.ι = V.ι := P.homOfLE_ι hVW
  have hip : V.ι ≫ p = i ≫ (W.ι ≫ p) := by rw [← Category.assoc, hiι]
  have hiq : V.ι ≫ q = i ≫ (W.ι ≫ q) := by rw [← Category.assoc, hiι]
  have hmemΩ : ∀ v : V.toScheme, i v ∈ Ω := by
    rw [Scheme.Opens.forall_toScheme]
    intro z hz
    have hz' := hz
    rw [hV] at hz'
    obtain ⟨t, htΩ, hteq⟩ := hz'
    have hieq : i ⟨z, hz⟩ = t := by
      rw [hi, Scheme.homOfLE_apply' hVW z hz]
      exact (Subtype.ext hteq).symm
    rw [hieq]
    exact htΩ
  have hVmod : (Scheme.Modules.pullback (V.ι ≫ p)).obj F ≅
      (Scheme.Modules.pullback i).obj G := by
    rw [hip, hG]
    exact ((Scheme.Modules.pullbackComp i (W.ι ≫ p)).app F).symm
  refine ⟨V, fun z hz => ⟨⟨z, hAW hz⟩, hmemΩ' ⟨z, hAW hz⟩ (hA z hz), rfl⟩, hVW, ?_, ?_⟩
  · rw [hip]
    exact isFinitePresentation_pullback_comp i (W.ι ≫ p) F hWfp
  · intro v
    rw [(isFlatOverAt_iff_of_moduleIso (V.ι ≫ q).toLRSHom.toShHom hVmod v), hiq]
    exact (isFlatOverAt_iff_modulePullback_isFlatOverAt i (W.ι ≫ q) G v
      (Flat.stalkMap i v)).mp (hmemΩ v)

/-- **Transporting an open with finitely presented pullback along a morphism of bases.** Let
`c : T₂ ⟶ T₁` be a morphism over `S` and let `V₁` be an open of `X ×_S T₁` on which the pullback
of `F` is of finite presentation. Then the induced morphism `m : X ×_S T₂ ⟶ X ×_S T₁` lies over
`X`, and the inverse image of `V₁` under `m` is an open of `X ×_S T₂` on which the pullback of
`F` is of finite presentation.

The morphism `m` is returned together with the two properties, so that a caller may transfer
membership in `V₁` to membership in the inverse image. -/
theorem exists_hom_pullback_isFinitePresentation_preimage {X S T₁ T₂ : Scheme.{u}} (f : X ⟶ S)
    {b₁ : T₁ ⟶ S} {b₂ : T₂ ⟶ S} (c : T₂ ⟶ T₁) (hc : c ≫ b₁ = b₂) (F : X.Modules)
    (V₁ : (pullback f b₁).Opens)
    (h₁ : ((Scheme.Modules.pullback (V₁.ι ≫ pullback.fst f b₁)).obj F).IsFinitePresentation) :
    ∃ (m : pullback f b₂ ⟶ pullback f b₁) (V₂ : (pullback f b₂).Opens),
      (∀ z : ↑(pullback f b₂), pullback.fst f b₁ (m z) = pullback.fst f b₂ z) ∧
      (∀ z : ↑(pullback f b₂), m z ∈ V₁ → z ∈ V₂) ∧
      ((Scheme.Modules.pullback (V₂.ι ≫ pullback.fst f b₂)).obj F).IsFinitePresentation := by
  set m : pullback f b₂ ⟶ pullback f b₁ :=
    pullback.map f b₂ f b₁ (𝟙 X) c (𝟙 S) (by simp) (by simpa using hc.symm) with hm
  have hmfst : m ≫ pullback.fst f b₁ = pullback.fst f b₂ := by
    simp only [hm, pullback.map, pullback.lift_fst, Category.comp_id]
  refine ⟨m, m ⁻¹ᵁ V₁, fun z => ?_, fun z hz => hz, ?_⟩
  · simpa only [Scheme.Hom.comp_apply] using congrArg (fun k : pullback f b₂ ⟶ X => k z) hmfst
  · have heq : (m ⁻¹ᵁ V₁).ι ≫ pullback.fst f b₂ =
        (m ∣_ V₁) ≫ (V₁.ι ≫ pullback.fst f b₁) := by
      rw [← hmfst, ← Category.assoc, ← morphismRestrict_ι m V₁, Category.assoc]
    rw [heq]
    exact isFinitePresentation_pullback_comp _ _ F h₁

/-- **Finite presentation of the pullback of a module to a union of opens.** If the pullback of
a quasi-coherent module `F` along `(V i).ι ≫ g` is of finite presentation for every member of a
family of opens of `P`, then so is its pullback along the restriction of `g` to the union: the
opens `V i` form an open — hence fpqc — covering of that union, and finite presentation descends
along an fpqc covering by Tag 05B0. -/
theorem isFinitePresentation_pullback_ι_iSup {P X : Scheme.{u}} (g : P ⟶ X) (F : X.Modules)
    [F.IsQuasicoherent] {I : Type u} (V : I → P.Opens)
    (h : ∀ i, ((Scheme.Modules.pullback ((V i).ι ≫ g)).obj F).IsFinitePresentation) :
    ((Scheme.Modules.pullback ((⨆ i, V i).ι ≫ g)).obj F).IsFinitePresentation := by
  have hle : ∀ i, V i ≤ ⨆ j, V j := le_iSup V
  have hqc : ((Scheme.Modules.pullback ((⨆ i, V i).ι ≫ g)).obj F).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback ((⨆ i, V i).ι ≫ g) F inferInstance
  let 𝒰z : (⨆ i, V i).toScheme.Cover Scheme.zariskiPrecoverage :=
    Scheme.Cover.mkOfCovers I (fun i => (V i).toScheme) (fun i => P.homOfLE (hle i))
      (by
        rintro ⟨z, hz⟩
        obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
        exact ⟨i, ⟨z, hi⟩, Subtype.ext (Scheme.homOfLE_apply (hle i) ⟨z, hi⟩)⟩)
  let 𝒰 : (⨆ i, V i).toScheme.Cover Scheme.fpqcPrecoverage :=
    { I₀ := 𝒰z.I₀
      X := 𝒰z.X
      f := 𝒰z.f
      mem₀ := Scheme.zariskiPrecoverage_le_fpqcPrecoverage _ 𝒰z.mem₀ }
  refine isFinitePresentation_of_pullback_fpqcCover _ 𝒰 fun i => ?_
  have hcomp : ((Scheme.Modules.pullback
      (P.homOfLE (hle i) ≫ ((⨆ j, V j).ι ≫ g))).obj F).IsFinitePresentation := by
    rw [← Category.assoc, P.homOfLE_ι (hle i)]
    exact h i
  exact (SheafOfModules.isFinitePresentation (V i).toScheme.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.pullbackComp (P.homOfLE (hle i)) ((⨆ j, V j).ι ≫ g)).app F).symm hcomp

/-- **Stacks Project, Tag 05KU.** Let `f : X ⟶ S` be of finite presentation, let `F` be a
quasi-coherent `𝒪_X`-module of finite type, and let `s` be a point of `S` such that `F` is flat
over `S` at every point of the fibre `X_s`. Then there are an elementary étale neighbourhood
`(S', s')` of `(S, s)` and an open `V ⊆ X ×_S Spec 𝒪_{S', s'}` containing the whole fibre
`X_s = X ×_S s'` such that the pullback of `F` to `V` is of finite presentation as an
`𝒪_V`-module and flat over `𝒪_{S', s'}`.

The fibre `X ×_S s'` is read as the set of points of `X ×_S Spec 𝒪_{S', s'}` whose image in `X`
lies over `s`. -/
@[stacks 05KU]
theorem exists_elementaryEtaleNeighborhood_isFinitePresentation_isFlatOver_fiber
    {X S : Scheme.{u}} (f : X ⟶ S) (hf : FinitePresentation f) (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (s : S)
    (hflat : ∀ x : X, f x = s → IsFlatOverAt f.toLRSHom.toShHom F x) :
    ∃ (U : EtaleNeighborhood S s) (_ : U.IsElementary)
      (V : (pullback f (U.scheme.fromSpecStalk U.point ≫ U.toBase)).Opens),
      (∀ z : ↑(pullback f (U.scheme.fromSpecStalk U.point ≫ U.toBase)),
          f (pullback.fst f (U.scheme.fromSpecStalk U.point ≫ U.toBase) z) = s → z ∈ V) ∧
      ((Scheme.Modules.pullback (V.ι ≫ pullback.fst f
          (U.scheme.fromSpecStalk U.point ≫ U.toBase))).obj F).IsFinitePresentation ∧
      IsFlatOver
        (V.ι ≫ pullback.snd f
          (U.scheme.fromSpecStalk U.point ≫ U.toBase)).toLRSHom.toShHom
        ((Scheme.Modules.pullback (V.ι ≫ pullback.fst f
          (U.scheme.fromSpecStalk U.point ≫ U.toBase))).obj F) := by
  classical
  have hlfp : LocallyOfFinitePresentation f := hf.1
  have hqcf : QuasiCompact f := hf.2.1
  -- Tag 05I5 at every point of the fibre, uniformly over a neighbourhood in the fibre
  choose Un hUn Wn hWno hwWn Vn hVnfp hVnmem using fun w : f.fiber s =>
    exists_elementaryEtaleNeighborhood_isFinitePresentation_nhds f F w
      (hflat _ (f.apply_fiberι s w))
  -- the fibre is quasi-compact, so finitely many of the neighbourhoods `Wn w` cover it
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover Wn fun w => (hWno w).mem_nhds (hwWn w)
  -- Tag 057B: one elementary étale neighbourhood dominates those finitely many
  obtain ⟨N, hN⟩ := IsCofiltered.inf_objs_exists
    (t.image fun w => (⟨Un w, hUn w⟩ : ElementaryEtaleNeighborhood S s))
  set b' : Spec (N.obj.scheme.presheaf.stalk N.obj.point) ⟶ S :=
    N.obj.scheme.fromSpecStalk N.obj.point ≫ N.obj.toBase with hb'
  -- transport each piece to the base change along the dominating neighbourhood
  have key : ∀ w ∈ t, ∃ V' : (pullback f b').Opens,
      ((Scheme.Modules.pullback (V'.ι ≫ pullback.fst f b')).obj F).IsFinitePresentation ∧
      ∀ w' ∈ Wn w, ∀ z : ↑(pullback f b'),
        pullback.fst f b' z = f.fiberι s w' → z ∈ V' := by
    intro w hwt
    obtain ⟨φ⟩ := hN (Finset.mem_image_of_mem _ hwt)
    obtain ⟨c, hc⟩ := exists_hom_specStalk_of_apply_eq φ.hom.hom N.obj.point (Un w).point
      φ.hom.map_point
    have hcb : c ≫ ((Un w).scheme.fromSpecStalk (Un w).point ≫ (Un w).toBase) = b' := by
      rw [← Category.assoc, hc, Category.assoc, φ.hom.over, hb']
    obtain ⟨m, V₂, hmfst, hmem, hfp⟩ :=
      exists_hom_pullback_isFinitePresentation_preimage f c hcb F (Vn w) (hVnfp w)
    exact ⟨V₂, hfp, fun w' hw' z hz => hmem z (hVnmem w w' hw' (m z) ((hmfst z).trans hz))⟩
  choose! V' hV'fp hV'mem using key
  -- the union contains the whole fibre
  have hfib : ∀ z : ↑(pullback f b'), f (pullback.fst f b' z) = s →
      z ∈ ⨆ k : {w // w ∈ t}, V' k.1 := by
    intro z hz
    have hw'eq : f.fiberι s ((f.fiberHomeo s).symm ⟨pullback.fst f b' z, hz⟩) =
      pullback.fst f b' z := f.fiberι_fiberHomeo_symm s _
    have hmem : (f.fiberHomeo s).symm ⟨pullback.fst f b' z, hz⟩ ∈ ⋃ w ∈ t, Wn w := by
      rw [ht]
      exact Set.mem_univ _
    obtain ⟨w, hwt, hw'W⟩ := Set.mem_iUnion₂.mp hmem
    exact le_iSup (fun k : {w // w ∈ t} => V' k.1) ⟨w, hwt⟩ (hV'mem w hwt _ hw'W z hw'eq.symm)
  -- finite presentation on the union, by Tag 05B0
  have hVtotfp : ((Scheme.Modules.pullback
      ((⨆ k : {w // w ∈ t}, V' k.1).ι ≫ pullback.fst f b')).obj F).IsFinitePresentation :=
    isFinitePresentation_pullback_ι_iSup (pullback.fst f b') F _ fun j => hV'fp j.1 j.2
  -- shrink to the flat locus; the whole fibre survives
  obtain ⟨V, hAV, -, hVfp, hVflat⟩ := exists_open_isFinitePresentation_isFlatOver_of_subset
    (IsPullback.of_hasPullback f b') F _ hVtotfp
    {z : ↑(pullback f b') | f (pullback.fst f b' z) = s} (fun z hz => hfib z hz)
    fun z hz => hflat _ hz
  exact ⟨N.obj, N.property, V, fun z hz => hAV hz, hVfp, hVflat⟩

end AlgebraicGeometry

end
