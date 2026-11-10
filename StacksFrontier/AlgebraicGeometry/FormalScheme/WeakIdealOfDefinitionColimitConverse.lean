module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionColimit
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionKernelOfThickening

/-!
# A colimit of schemes along thickenings gives a fundamental system

Let `𝔛` be a formal scheme in the sense of McQuillan whose functor of points `h_𝔛` is a colimit, as
in Stacks 0AIU, of a directed system of schemes `X_λ` along thickenings: the comparison map
`colim h_{X_λ} → h_𝔛` is bijective Zariski locally. This file proves the direction of **Stacks
0AIV** going from such a colimit to a fundamental system of weak ideals of definition: the kernels
of the morphisms `X_λ → 𝔛` form one.

The argument runs as follows. Each stage `h_{X_λ} → h_𝔛` is a monomorphism: two morphisms
`T → X_λ` with the same image in `h_𝔛` agree Zariski locally in the filtered colimit, hence after a
transition `X_λ → X_μ`, which is a monomorphism. Each stage is moreover a thickening of `h_𝔛`:
along a point `T → 𝔛`, the morphisms `T' → T` factoring through `X_λ` form a Zariski sheaf, and
over an open `V ⊆ T` on which the point lifts to some `X_μ` with `μ ≥ λ`, they are the morphisms
factoring through the base change `V ×_{X_μ} X_λ → V` of the thickening `X_λ → X_μ`; such a
subfunctor of `h_T` is represented by a thickening of `T`. The kernels of the stages are then weak
ideals of definition cut out by their sections over the weak affine formal opens, by
`AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf`
`.isWeakIdealOfDefinitionOn_ker_of_isThickening` and
`AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.isCutOutOn_ker_of_isThickening`.
They are directed because the transitions are compatible with the morphisms to `𝔛`. They become
small: over a weak affine formal open `𝔘 ≅ Spfw A`, a neighbourhood of zero contains the image of a
weak ideal of definition `L` of `A`, and the quotient point `Spec (A/L) → 𝔛`, whose source is
quasi-compact, lifts Zariski locally to finitely many stages, hence to the kernel of a single later
stage, which it therefore kills.

## Main results

* `AlgebraicGeometry.exists_isThickening_forall_mem_iff`: a Zariski sheaf of morphisms into a
  scheme `T`, cut out over the members of an open cover by thickenings, is the sheaf of morphisms
  factoring through a thickening of `T`.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.injective_coconeMap_app`: the
  stages of the colimit are monomorphisms.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.isThickening_presheaf_coconeMap`:
  the stages of the colimit are thickenings of `h_𝔛`.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf`
  `.exists_isFundamentalSystem_of_isColimitOfThickenings`: a colimit of schemes along thickenings
  gives a nonempty directed fundamental system of weak ideals of definition, each cut out by its
  sections over the weak affine formal opens.

## Implementation notes

The thickening `W → T` representing a subfunctor of `h_T` is glued from the local pieces by the
local representability criterion `AlgebraicGeometry.Scheme.LocalRepresentability.representableBy`:
each piece `P i → V i ⊆ T` is a relatively representable open immersion into the subfunctor, its
base change along `k : T' → T` being the open subscheme `k⁻¹(V i)`.

## References

* [Stacks Project, Tag 0AIV](https://stacks.math.columbia.edu/tag/0AIV)
* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-! ### Subfunctors of a representable cut out locally by thickenings -/

namespace LocalThickening

variable {T : Scheme.{u}} {G : Subfunctor (yoneda.obj T)} {ι : Type u} {V : ι → T.Opens}
  {P : ι → Scheme.{u}} {p : ∀ i, P i ⟶ (V i).toScheme}
  (hGp : ∀ i {T' : Scheme.{u}} (k : T' ⟶ (V i).toScheme),
    k ≫ (V i).ι ∈ G.obj (op T') ↔ ∃ m : T' ⟶ P i, m ≫ p i = k)
  (hp : ∀ i, Stacks.Thickenings.IsThickening (p i))

/-- The element of the subfunctor given by a local piece `P i → V i ⊆ T`. -/
def pieceElement (i : ι) : G.toFunctor.obj (op (P i)) :=
  ⟨p i ≫ (V i).ι, (hGp i (p i)).2 ⟨𝟙 _, Category.id_comp _⟩⟩

/-- The morphism `h_{P i} → G` of a local piece. -/
noncomputable def pieceMap (i : ι) : yoneda.obj (P i) ⟶ G.toFunctor :=
  yonedaEquiv.symm (pieceElement hGp i)

/-- The morphism of a local piece acts by composition with `P i → V i ⊆ T`. -/
theorem pieceMap_app_val (i : ι) {T' : Scheme.{u}} (x : T' ⟶ P i) :
    ((pieceMap hGp i).app (op T') x).1 = x ≫ p i ≫ (V i).ι :=
  rfl

/-- A morphism `h_{T'} → G` acts by precomposition on its own point. -/
theorem app_val_eq {T' T'' : Scheme.{u}} (g : yoneda.obj T' ⟶ G.toFunctor) (y : T'' ⟶ T') :
    (g.app (op T'') y).1 = y ≫ (yonedaEquiv g).1 := by
  have : g.app (op T'') y = G.toFunctor.map y.op (yonedaEquiv g) := by
    rw [yonedaEquiv_naturality, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  rw [this]
  rfl

/-- A morphism of schemes whose points all lie in an open factors through its inclusion. -/
private theorem range_subset_range_ι_of_forall_mem {X Y : Scheme.{u}} (U : Y.Opens) (f : X ⟶ Y)
    (h : ∀ x, f x ∈ U) : Set.range f ⊆ Set.range U.ι := by
  rw [Scheme.Opens.range_ι]
  exact Set.range_subset_iff.2 h

omit hGp in
/-- The preimage of `V i` under `k : T' → T` maps into `V i`. -/
theorem range_preimage_ι_comp_subset (i : ι) {T' : Scheme.{u}} (k : T' ⟶ T) :
    Set.range ((k ⁻¹ᵁ V i).ι ≫ k) ⊆ Set.range (V i).ι := by
  exact range_subset_range_ι_of_forall_mem _ _ fun y => y.2

variable (V) in
/-- The restriction `k⁻¹(V i) → V i` of a morphism `k : T' → T`. -/
noncomputable def restrictV (i : ι) {T' : Scheme.{u}} (k : T' ⟶ T) :
    (k ⁻¹ᵁ V i).toScheme ⟶ (V i).toScheme :=
  IsOpenImmersion.lift (V i).ι ((k ⁻¹ᵁ V i).ι ≫ k) (range_preimage_ι_comp_subset i k)

/-- The restriction `k⁻¹(V i) → V i` followed by the inclusion `V i ⊆ T` is the composite
`k⁻¹(V i) ⊆ T' → T`. -/
theorem restrictV_ι (i : ι) {T' : Scheme.{u}} (k : T' ⟶ T) :
    restrictV V i k ≫ (V i).ι = (k ⁻¹ᵁ V i).ι ≫ k :=
  IsOpenImmersion.lift_fac _ _ _

/-- The restriction to `k⁻¹(V i)` of a morphism `k` of the subfunctor is in the subfunctor. -/
theorem restrictV_mem (i : ι) {T' : Scheme.{u}} {k : T' ⟶ T} (hk : k ∈ G.obj (op T')) :
    restrictV V i k ≫ (V i).ι ∈ G.obj (op (k ⁻¹ᵁ V i).toScheme) := by
  rw [restrictV_ι]
  exact G.map (k ⁻¹ᵁ V i).ι.op hk

/-- The lift `k⁻¹(V i) → P i` of a morphism `k : T' → T` in the subfunctor. -/
noncomputable def pieceLift (i : ι) {T' : Scheme.{u}} {k : T' ⟶ T} (hk : k ∈ G.obj (op T')) :
    (k ⁻¹ᵁ V i).toScheme ⟶ P i :=
  ((hGp i _).1 (restrictV_mem i hk)).choose

/-- The lift `k⁻¹(V i) → P i` followed by the piece `P i → V i` is the restriction
`k⁻¹(V i) → V i`. -/
theorem pieceLift_comp (i : ι) {T' : Scheme.{u}} {k : T' ⟶ T} (hk : k ∈ G.obj (op T')) :
    pieceLift hGp i hk ≫ p i = restrictV V i k :=
  ((hGp i _).1 (restrictV_mem i hk)).choose_spec

/-- The lift `k⁻¹(V i) → P i` followed by `P i → V i ⊆ T` is the composite `k⁻¹(V i) ⊆ T' → T`. -/
theorem pieceLift_comp_ι (i : ι) {T' : Scheme.{u}} {k : T' ⟶ T} (hk : k ∈ G.obj (op T')) :
    pieceLift hGp i hk ≫ p i ≫ (V i).ι = (k ⁻¹ᵁ V i).ι ≫ k := by
  rw [← Category.assoc, pieceLift_comp, restrictV_ι]

include hp in
/-- A local piece `P i → V i ⊆ T` is a monomorphism. -/
theorem mono_comp_ι (i : ι) : Mono (p i ≫ (V i).ι) := by
  have := (hp i).1
  infer_instance

include hp in
/-- **The local pieces are relatively representable open immersions**: the base change of a
local piece along `k : T' → T` in the subfunctor is the open subscheme `k⁻¹(V i) ⊆ T'`. -/
theorem isOpenImmersion_presheaf_pieceMap (i : ι) :
    IsOpenImmersion.presheaf (pieceMap hGp i) := by
  refine MorphismProperty.relative.of_exists fun T' g => ?_
  set k := (yonedaEquiv g).1
  have hk : k ∈ G.obj (op T') := (yonedaEquiv g).2
  have := mono_comp_ι hp i
  refine ⟨_, yoneda.map (pieceLift hGp i hk), (k ⁻¹ᵁ V i).ι, ?_, inferInstance⟩
  refine IsPullback.of_forall_isPullback_app fun T'' => ?_
  induction T'' using Opposite.rec with
  | op T'' =>
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext x
    refine Subtype.ext ?_
    change ((pieceMap hGp i).app (op T'') (x ≫ pieceLift hGp i hk)).1 =
      (g.app (op T'') (x ≫ (k ⁻¹ᵁ V i).ι)).1
    rw [pieceMap_app_val, app_val_eq]
    change x ≫ pieceLift hGp i hk ≫ p i ≫ (V i).ι = x ≫ (k ⁻¹ᵁ V i).ι ≫ k
    rw [pieceLift_comp_ι]
  · rintro (x₁ : T'' ⟶ _) (x₂ : T'' ⟶ _) ⟨-, h₂⟩
    exact (cancel_mono (k ⁻¹ᵁ V i).ι).mp h₂
  · intro (x : T'' ⟶ P i) (y : T'' ⟶ T') hxy
    have hxy' : x ≫ p i ≫ (V i).ι = y ≫ k := by
      have := congrArg Subtype.val hxy
      rwa [pieceMap_app_val, app_val_eq] at this
    have hy : Set.range y ⊆ Set.range (k ⁻¹ᵁ V i).ι :=
      range_subset_range_ι_of_forall_mem _ _ fun z => by
        change (y ≫ k) z ∈ V i
        rw [← hxy']
        exact ((x ≫ p i) z).2
    refine ⟨IsOpenImmersion.lift _ y hy, ?_, IsOpenImmersion.lift_fac _ _ _⟩
    refine (cancel_mono (p i ≫ (V i).ι)).mp ?_
    change (IsOpenImmersion.lift _ y hy ≫ pieceLift hGp i hk) ≫ p i ≫ (V i).ι = _
    rw [Category.assoc, pieceLift_comp_ι, ← Category.assoc, IsOpenImmersion.lift_fac, hxy']

variable (G) in
/-- A subfunctor of `h_T` which is a Zariski sheaf, as a sheaf. -/
noncomputable def subfunctorSheaf (hG : Presieve.IsSheaf Scheme.zariskiTopology G.toFunctor) :
    Sheaf Scheme.zariskiTopology.{u} (Type u) :=
  ⟨G.toFunctor, (isSheaf_iff_isSheaf_of_type _ _).mpr hG⟩

/-- The local pieces, as a family of morphisms into the sheaf. -/
noncomputable abbrev pieceFamily (hG : Presieve.IsSheaf Scheme.zariskiTopology G.toFunctor)
    (i : ι) : yoneda.obj (P i) ⟶ (subfunctorSheaf G hG).1 :=
  pieceMap hGp i

/-- **The local pieces are jointly surjective, Zariski locally**, as soon as the opens `V i`
cover `T`. -/
theorem isLocallySurjective_sigmaDesc_pieceMap
    (hG : Presieve.IsSheaf Scheme.zariskiTopology G.toFunctor) (hV : ∀ x : T, ∃ i, x ∈ V i) :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc (pieceFamily hGp hG)) := by
  refine ⟨fun {T'} k => ?_⟩
  choose c hc using hV
  let k' : T' ⟶ T := k.1
  have hk : k' ∈ G.obj (op T') := k.2
  rw [Scheme.mem_grothendieckTopology_iff]
  refine ⟨Scheme.Cover.mkOfCovers T' (fun q => (k' ⁻¹ᵁ V (c (k' q))).toScheme)
    (fun q => (k' ⁻¹ᵁ V (c (k' q))).ι) (fun q => ⟨q, ⟨q, hc _⟩, rfl⟩), ?_⟩
  rintro _ _ ⟨q⟩
  refine ⟨(Sigma.ι (fun i => yoneda.obj (P i)) (c (k' q))).app _
    (pieceLift hGp (c (k' q)) hk), ?_⟩
  have h := congrArg (fun η => η.app (op (k' ⁻¹ᵁ V (c (k' q))).toScheme)
      (pieceLift hGp (c (k' q)) hk))
    (Sigma.ι_comp_desc (pieceFamily hGp hG) (c (k' q)))
  simp only [NatTrans.comp_app, types_comp_apply] at h
  exact h.trans (Subtype.ext (pieceLift_comp_ι hGp (c (k' q)) hk))

variable (hG : Presieve.IsSheaf Scheme.zariskiTopology G.toFunctor) (hV : ∀ x : T, ∃ i, x ∈ V i)

/-- The scheme glued from the local pieces. -/
noncomputable def glued : Scheme.{u} :=
  (Scheme.LocalRepresentability.glueData (F := subfunctorSheaf G hG) (f := pieceFamily hGp hG)
    (fun i => isOpenImmersion_presheaf_pieceMap hGp hp i)).glued

/-- The glued scheme represents the subfunctor. -/
noncomputable def gluedRepresentableBy : G.toFunctor.RepresentableBy (glued hGp hp hG) :=
  have := isLocallySurjective_sigmaDesc_pieceMap hGp hG hV
  Scheme.LocalRepresentability.representableBy (F := subfunctorSheaf G hG)
    (f := pieceFamily hGp hG) (fun i => isOpenImmersion_presheaf_pieceMap hGp hp i)

/-- The projection of the glued scheme to `T`. -/
noncomputable def gluedProj : glued hGp hp hG ⟶ T :=
  ((gluedRepresentableBy hGp hp hG hV).homEquiv (𝟙 _)).1

/-- The element of the subfunctor corresponding to a morphism `m` into the glued scheme is the
composite of `m` with the projection to `T`. -/
theorem gluedRepresentableBy_homEquiv_val {T' : Scheme.{u}} (m : T' ⟶ glued hGp hp hG) :
    ((gluedRepresentableBy hGp hp hG hV).homEquiv m).1 = m ≫ gluedProj hGp hp hG hV := by
  rw [(gluedRepresentableBy hGp hp hG hV).homEquiv_eq]
  rfl

/-- **The glued scheme represents the subfunctor** through its projection to `T`. -/
theorem mem_iff_exists_comp_gluedProj {T' : Scheme.{u}} (k : T' ⟶ T) :
    k ∈ G.obj (op T') ↔ ∃ m : T' ⟶ glued hGp hp hG, m ≫ gluedProj hGp hp hG hV = k := by
  refine ⟨fun hk => ?_, ?_⟩
  · set e := gluedRepresentableBy hGp hp hG hV
    exact ⟨e.homEquiv.symm ⟨k, hk⟩, (gluedRepresentableBy_homEquiv_val hGp hp hG hV _).symm.trans
      (congrArg Subtype.val (e.homEquiv.apply_symm_apply ⟨k, hk⟩))⟩
  · rintro ⟨m, rfl⟩
    rw [← gluedRepresentableBy_homEquiv_val]
    exact ((gluedRepresentableBy hGp hp hG hV).homEquiv m).2

/-- The projection of the glued scheme to `T` is a monomorphism of schemes. -/
instance mono_gluedProj : Mono (gluedProj hGp hp hG hV) := by
  refine ⟨fun {T'} m₁ m₂ h => (gluedRepresentableBy hGp hp hG hV).homEquiv.injective
    (Subtype.ext ?_)⟩
  rw [gluedRepresentableBy_homEquiv_val, gluedRepresentableBy_homEquiv_val, h]

/-- **Over `V i` the glued scheme is the local piece**: the restriction of the projection over
`V i` is, up to isomorphism, `P i → V i`. -/
theorem exists_isIso_morphismRestrict_gluedProj (i : ι) :
    ∃ e : (gluedProj hGp hp hG hV ⁻¹ᵁ V i).toScheme ⟶ P i, IsIso e ∧
      gluedProj hGp hp hG hV ∣_ V i = e ≫ p i := by
  set w := gluedProj hGp hp hG hV
  have hw : w ∈ G.obj (op (glued hGp hp hG)) :=
    (mem_iff_exists_comp_gluedProj hGp hp hG hV w).2 ⟨𝟙 _, Category.id_comp _⟩
  have h₁ : (w ∣_ V i) ≫ (V i).ι ∈ G.obj (op (w ⁻¹ᵁ V i).toScheme) := by
    rw [morphismRestrict_ι]
    exact G.map (w ⁻¹ᵁ V i).ι.op hw
  obtain ⟨e, he⟩ := (hGp i _).1 h₁
  obtain ⟨n, hn⟩ : ∃ n : P i ⟶ glued hGp hp hG, n ≫ w = p i ≫ (V i).ι :=
    (mem_iff_exists_comp_gluedProj hGp hp hG hV _).1 (pieceElement hGp i).2
  have hrange : Set.range n ⊆ Set.range (w ⁻¹ᵁ V i).ι :=
    range_subset_range_ι_of_forall_mem _ _ fun z => by
      change (n ≫ w) z ∈ V i
      rw [hn]
      exact ((p i) z).2
  set n' := IsOpenImmersion.lift (w ⁻¹ᵁ V i).ι n hrange
  have hn' : n' ≫ (w ⁻¹ᵁ V i).ι = n := IsOpenImmersion.lift_fac _ _ _
  have := mono_comp_ι hp i
  refine ⟨e, ⟨n', ?_, ?_⟩, he.symm⟩
  · refine (cancel_mono ((w ⁻¹ᵁ V i).ι ≫ w)).mp ?_
    rw [Category.id_comp, Category.assoc, ← Category.assoc n', hn', hn, ← Category.assoc, he,
      morphismRestrict_ι]
  · refine (cancel_mono (p i ≫ (V i).ι)).mp ?_
    rw [Category.id_comp, Category.assoc, ← Category.assoc e, he, morphismRestrict_ι,
      ← Category.assoc, hn', hn]

/-- **The projection of the glued scheme is a thickening**: being a closed immersion and being
surjective are local on the target. -/
theorem isThickening_gluedProj : Stacks.Thickenings.IsThickening (gluedProj hGp hp hG hV) := by
  have hcov : iSup V = ⊤ := iSup_eq_top_of_forall_exists_mem _ hV
  have hres : ∀ i, Stacks.Thickenings.IsThickening (gluedProj hGp hp hG hV ∣_ V i) := fun i => by
    obtain ⟨e, he, heq⟩ := exists_isIso_morphismRestrict_gluedProj hGp hp hG hV i
    rw [heq]
    exact Stacks.Thickenings.isThickening_comp (Stacks.Thickenings.isThickening_of_isIso e) (hp i)
  refine ⟨IsZariskiLocalAtTarget.of_iSup_eq_top _ hcov fun i => (hres i).1, ?_⟩
  exact (IsZariskiLocalAtTarget.of_iSup_eq_top (P := @Surjective) _ hcov fun i =>
    (⟨(hres i).2⟩ : Surjective _)).surj

end LocalThickening

/-- **A Zariski sheaf of morphisms into a scheme, cut out locally by thickenings, is represented by
a thickening.** Let `G ⊆ h_T` be a subfunctor which is a Zariski sheaf, and let `V i` be opens
covering `T` with thickenings `P i → V i` such that a morphism `k : T' → V i` lies in `G` exactly
when it factors through `P i`. Then there is a thickening `W → T` through which exactly the
morphisms of `G` factor. -/
theorem exists_isThickening_forall_mem_iff {T : Scheme.{u}} (G : Subfunctor (yoneda.obj T))
    (hG : Presieve.IsSheaf Scheme.zariskiTopology G.toFunctor) {ι : Type u} (V : ι → T.Opens)
    (hV : ∀ x : T, ∃ i, x ∈ V i) {P : ι → Scheme.{u}} (p : ∀ i, P i ⟶ (V i).toScheme)
    (hp : ∀ i, Stacks.Thickenings.IsThickening (p i))
    (hGp : ∀ i {T' : Scheme.{u}} (k : T' ⟶ (V i).toScheme),
      k ≫ (V i).ι ∈ G.obj (op T') ↔ ∃ m : T' ⟶ P i, m ≫ p i = k) :
    ∃ (W : Scheme.{u}) (w : W ⟶ T), Stacks.Thickenings.IsThickening w ∧
      ∀ {T' : Scheme.{u}} (k : T' ⟶ T), k ∈ G.obj (op T') ↔ ∃ m : T' ⟶ W, m ≫ w = k :=
  ⟨_, _, LocalThickening.isThickening_gluedProj hGp hp hG hV,
    fun k => LocalThickening.mem_iff_exists_comp_gluedProj hGp hp hG hV k⟩

namespace LocallyTopologicallyRingedSpace.IdealSheaf

section Colimit

variable {𝔛 : McQuillanFormalScheme.{u}} {Λ : Type u} [Preorder Λ] {D : Λ ⥤ Scheme.{u}}
  (ι : D ⋙ yoneda ⟶ (Functor.const Λ).obj (mcQuillanFormalSchemePoints 𝔛))

/-- The morphism `h_{X_λ} → h_𝔛` of a stage of the colimit. -/
noncomputable abbrev coconeMap (l : Λ) : yoneda.obj (D.obj l) ⟶ mcQuillanFormalSchemePoints 𝔛 :=
  ι.app l

/-- The stages are compatible with the transitions. -/
theorem coconeMap_app_comp_map {l m : Λ} (g : l ⟶ m) {T : Scheme.{u}} (b : T ⟶ D.obj l) :
    (coconeMap ι m).app (op T) (b ≫ D.map g) = (coconeMap ι l).app (op T) b := by
  have h := ι.naturality g
  simp only [Functor.const_obj_map] at h
  exact congrArg (fun η => η.app (op T) b) h

/-- The comparison map from the colimit restricts on each stage to the morphism of that stage. -/
theorem colimitDesc_app_ι (l : Λ) {T : Scheme.{u}} (a : T ⟶ D.obj l) :
    (colimit.desc (D ⋙ yoneda) (Cocone.mk _ ι)).app (op T)
        ((colimit.ι (D ⋙ yoneda) l).app (op T) a) = (coconeMap ι l).app (op T) a :=
  congrArg (fun η => η.app (op T) a) (colimit.ι_desc (Cocone.mk _ ι) l)

/-- The kernel ideal sheaf of a later stage is contained in that of an earlier one. -/
theorem ker_coconeMap_le {l m : Λ} (h : l ≤ m) (W : Opens 𝔛.obj) :
    (ker (yonedaEquiv (coconeMap ι m)).hom).ideal W ≤
      (ker (yonedaEquiv (coconeMap ι l)).hom).ideal W := by
  have heq : (yonedaEquiv (coconeMap ι l)).hom =
      schemeToLTRS.map (𝟙 _ ≫ D.map (homOfLE h)) ≫ (yonedaEquiv (coconeMap ι m)).hom := by
    rw [← app_hom_eq_schemeToLTRS_map_comp, coconeMap_app_comp_map]
    rfl
  rw [heq]
  exact ker_le_ker_comp _ _ W

variable [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
  (hD : ∀ ⦃i j : Λ⦄ (g : i ⟶ j), Stacks.Thickenings.IsThickening (D.map g))
  (hinj : Presheaf.IsLocallyInjective Scheme.zariskiTopology
    (colimit.desc (D ⋙ yoneda) (Cocone.mk _ ι)))
  (hsurj : Presheaf.IsLocallySurjective Scheme.zariskiTopology
    (colimit.desc (D ⋙ yoneda) (Cocone.mk _ ι)))

include hD hinj in
/-- **The stages of the colimit are monomorphisms**: two morphisms `T → X_λ` with the same image in
`h_𝔛` agree Zariski locally in the colimit, hence, the colimit being filtered, after some
transition `X_λ → X_μ`, which is a thickening and hence a monomorphism. -/
theorem injective_coconeMap_app (l : Λ) (T : Scheme.{u}) :
    Function.Injective ((coconeMap ι l).app (op T)) := by
  intro a b hab
  have hS := Presheaf.equalizerSieve_mem Scheme.zariskiTopology
    (colimit.desc (D ⋙ yoneda) (Cocone.mk _ ι))
    ((colimit.ι (D ⋙ yoneda) l).app (op T) a) ((colimit.ι (D ⋙ yoneda) l).app (op T) b)
    ((colimitDesc_app_ι ι l a).trans (hab.trans (colimitDesc_app_ι ι l b).symm))
  have hsh : Presieve.IsSheaf Scheme.zariskiTopology (yoneda.obj (D.obj l)) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  refine (hsh _ hS).isSeparatedFor.ext fun U f hf => ?_
  have hf' : (colimit.ι (D ⋙ yoneda) l).app (op U) (f ≫ a) =
      (colimit.ι (D ⋙ yoneda) l).app (op U) (f ≫ b) :=
    (NatTrans.naturality_apply (colimit.ι (D ⋙ yoneda) l) f.op a).trans
      (hf.trans (NatTrans.naturality_apply (colimit.ι (D ⋙ yoneda) l) f.op b).symm)
  have hc := isColimitOfPreserves ((evaluation _ (Type u)).obj (op U))
    (colimit.isColimit (D ⋙ yoneda))
  obtain ⟨m, g, hg⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc (f ≫ a) (f ≫ b)).mp hf'
  have := (hD g).1
  exact (cancel_mono (D.map g)).mp hg

omit [Nonempty Λ] in
include hsurj in
/-- **Every point of `𝔛` lifts Zariski locally to a stage above any given one.** -/
theorem exists_coconeMap_app_eq {T : Scheme.{u}} (s : (mcQuillanFormalSchemePoints 𝔛).obj (op T))
    (q : T) (l : Λ) :
    ∃ (V : T.Opens) (m : Λ) (_ : l ≤ m) (b : V.toScheme ⟶ D.obj m), q ∈ V ∧
      (coconeMap ι m).app (op V.toScheme) b = (mcQuillanFormalSchemePoints 𝔛).map V.ι.op s := by
  have hS := Presheaf.imageSieve_mem Scheme.zariskiTopology
    (colimit.desc (D ⋙ yoneda) (Cocone.mk _ ι)) s
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hS
  obtain ⟨j, y, hy⟩ := 𝒰.exists_eq q
  have : IsOpenImmersion (𝒰.f j) := 𝒰.map_prop j
  let V : T.Opens := (𝒰.f j).opensRange
  have hmem : Presheaf.imageSieve (colimit.desc (D ⋙ yoneda) (Cocone.mk _ ι)) s V.ι := by
    have hj := h𝒰 _ _ (Presieve.ofArrows.mk j)
    have := Sieve.downward_closed _ hj
      (IsOpenImmersion.isoOfRangeEq V.ι (𝒰.f j) V.range_ι).hom
    rwa [IsOpenImmersion.isoOfRangeEq_hom_fac V.ι (𝒰.f j) V.range_ι] at this
  obtain ⟨x, hx⟩ := hmem
  obtain ⟨m', b', hb'⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ((evaluation _ (Type u)).obj (op V.toScheme))
      (colimit.isColimit (D ⋙ yoneda))) x
  obtain ⟨m, hlm, hm'm⟩ := exists_ge_ge l m'
  refine ⟨V, m, hlm, b' ≫ D.map (homOfLE hm'm), ⟨y, hy⟩, ?_⟩
  rw [coconeMap_app_comp_map]
  rw [← hb'] at hx
  exact (colimitDesc_app_ι ι m' b').symm.trans hx

/-! ### The base change of a stage along a point -/

/-- Naturality of two morphisms of presheaves into a common target: if they agree on `x` and `y`,
they agree on the restrictions of `x` and `y`. -/
private theorem app_map_eq_of_app_eq {C : Type*} [Category C] {F F' G : Cᵒᵖ ⥤ Type _}
    (η : F ⟶ G) (ζ : F' ⟶ G) {X Y : Cᵒᵖ} (g : X ⟶ Y) {x : F.obj X} {y : F'.obj X}
    (h : η.app X x = ζ.app X y) : η.app Y (F.map g x) = ζ.app Y (F'.map g y) :=
  (NatTrans.naturality_apply η g x).trans ((congrArg _ h).trans
    (NatTrans.naturality_apply ζ g y).symm)

/-- The morphisms `k : T' → T` whose composite with a point `t : h_T → h_𝔛` factors through the
stage `h_{X_λ} → h_𝔛`: the base change of the stage along `t`. -/
def coconePoints (l : Λ) {T : Scheme.{u}} (t : yoneda.obj T ⟶ mcQuillanFormalSchemePoints 𝔛) :
    Subfunctor (yoneda.obj T) where
  obj T' := {k | ∃ a : T'.unop ⟶ D.obj l, (coconeMap ι l).app T' a = t.app T' k}
  map {T₁ T₂} g k := by
    rintro ⟨a, ha⟩
    exact ⟨g.unop ≫ a, (NatTrans.naturality_apply (coconeMap ι l) g a).trans
      ((congrArg _ ha).trans (NatTrans.naturality_apply t g k).symm)⟩

include hD hinj in
/-- The base change of a stage along a point is a Zariski sheaf: local factorisations through the
stage glue, the stage being a monomorphism and `h_𝔛` a sheaf. -/
theorem isSheaf_coconePoints (l : Λ) {T : Scheme.{u}}
    (t : yoneda.obj T ⟶ mcQuillanFormalSchemePoints 𝔛) :
    Presieve.IsSheaf Scheme.zariskiTopology (coconePoints ι l t).toFunctor := by
  rw [Subfunctor.isSheaf_iff _
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj T))]
  intro T' k hk
  have hmem : ∀ ⦃U : Scheme.{u}⦄ (f : U ⟶ T'.unop),
      (coconePoints ι l t).sieveOfSection k f →
        ∃ a : U ⟶ D.obj l, (coconeMap ι l).app (op U) a = t.app (op U) (f ≫ k) :=
    fun _ _ hf => hf
  choose a ha using hmem
  have hsh : Presieve.IsSheaf Scheme.zariskiTopology (yoneda.obj (D.obj l)) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  let x : Presieve.FamilyOfElements (yoneda.obj (D.obj l))
      ((coconePoints ι l t).sieveOfSection k).arrows := fun _ f hf => a f hf
  have hx : x.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro U U' f g hf
    refine injective_coconeMap_app ι hD hinj l U' ?_
    change (coconeMap ι l).app _ (a (g ≫ f) _) = (coconeMap ι l).app _ (g ≫ a f hf)
    rw [ha, Category.assoc]
    exact (app_map_eq_of_app_eq _ _ g.op (ha f hf)).symm
  refine ⟨(hsh _ hk).amalgamate x hx, ?_⟩
  refine (isSheaf_zariskiTopology_mcQuillanFormalSchemePoints 𝔛 _ hk).isSeparatedFor.ext
    fun U f hf => ?_
  have h₁ := (hsh _ hk).isAmalgamation hx f hf
  refine (NatTrans.naturality_apply (coconeMap ι l) f.op _).symm.trans ?_
  refine ((congrArg ((coconeMap ι l).app (op U)) h₁).trans (ha f hf)).trans ?_
  exact NatTrans.naturality_apply t f.op k

/-- An open of `T` over which a point `t : h_T → h_𝔛` lifts to a stage `X_μ` above `X_λ`. -/
structure CoconeChart (l : Λ) {T : Scheme.{u}} (t : yoneda.obj T ⟶ mcQuillanFormalSchemePoints 𝔛)
    where
  /-- The open of `T`. -/
  V : T.Opens
  /-- The stage. -/
  m : Λ
  /-- The stage lies above `X_λ`. -/
  le : l ≤ m
  /-- The lift. -/
  b : V.toScheme ⟶ D.obj m
  /-- The lift lifts the point. -/
  app_eq : (coconeMap ι m).app (op V.toScheme) b = t.app (op V.toScheme) V.ι

namespace CoconeChart

variable {ι} {l : Λ} {T : Scheme.{u}} {t : yoneda.obj T ⟶ mcQuillanFormalSchemePoints 𝔛}

/-- The base change of the stage over the open of a chart, `V ×_{X_μ} X_λ → V`. -/
noncomputable abbrev proj (c : CoconeChart ι l t) :
    pullback c.b (D.map (homOfLE c.le)) ⟶ c.V.toScheme :=
  pullback.fst _ _

omit [IsDirected Λ (· ≤ ·)] [Nonempty Λ] in
include hD in
/-- The base change `V ×_{X_μ} X_λ → V` of the thickening `X_λ → X_μ` is a thickening. -/
theorem isThickening_proj (c : CoconeChart ι l t) : Stacks.Thickenings.IsThickening c.proj :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Stacks.Thickenings.IsThickening)
    (IsPullback.of_hasPullback _ _).flip (hD _)

include hD hinj in
/-- Over the open of a chart, the base change of the stage is `V ×_{X_μ} X_λ`. -/
theorem mem_coconePoints_iff (c : CoconeChart ι l t) {T' : Scheme.{u}} (k : T' ⟶ c.V.toScheme) :
    k ≫ c.V.ι ∈ (coconePoints ι l t).obj (op T') ↔ ∃ n, n ≫ c.proj = k := by
  refine ⟨fun ⟨a, ha⟩ => ?_, ?_⟩
  · have hab : a ≫ D.map (homOfLE c.le) = k ≫ c.b := by
      refine injective_coconeMap_app ι hD hinj c.m T' ?_
      rw [coconeMap_app_comp_map]
      exact ha.trans (app_map_eq_of_app_eq _ _ k.op c.app_eq).symm
    exact ⟨pullback.lift k a hab.symm, pullback.lift_fst _ _ _⟩
  · rintro ⟨n, rfl⟩
    refine ⟨n ≫ pullback.snd _ _, ?_⟩
    have hc : (n ≫ pullback.snd _ _) ≫ D.map (homOfLE c.le) = (n ≫ c.proj) ≫ c.b := by
      rw [Category.assoc, Category.assoc, pullback.condition]
    rw [← coconeMap_app_comp_map ι (homOfLE c.le), hc]
    exact app_map_eq_of_app_eq _ _ (n ≫ c.proj).op c.app_eq

omit [Nonempty Λ] in
include hsurj in
/-- The opens of the charts of a point cover its source. -/
theorem exists_mem (l : Λ) (t : yoneda.obj T ⟶ mcQuillanFormalSchemePoints 𝔛) (x : T) :
    ∃ c : CoconeChart ι l t, x ∈ c.V := by
  obtain ⟨V, m, hlm, b, hxV, hb⟩ := exists_coconeMap_app_eq ι hsurj (t.app (op T) (𝟙 T)) x l
  refine ⟨⟨V, m, hlm, b, hb.trans ?_⟩, hxV⟩
  exact (NatTrans.naturality_apply t V.ι.op (𝟙 T)).symm.trans (congrArg _ (Category.comp_id V.ι))

end CoconeChart

include hD hinj hsurj in
/-- **The stages of the colimit are thickenings of `h_𝔛`**: the base change of `h_{X_λ} → h_𝔛`
along a point `T → 𝔛` is represented by a thickening of `T`, being so over the opens of `T` on
which the point lifts to some `X_μ`, where it is the base change of the thickening
`X_λ → X_μ`. -/
theorem isThickening_presheaf_coconeMap (l : Λ) :
    MorphismProperty.presheaf (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
      (coconeMap ι l) := by
  have : MorphismProperty.RespectsIso
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
      (P := (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}))
  refine MorphismProperty.relative.of_exists fun T t => ?_
  obtain ⟨W, w, hw, hWG⟩ := exists_isThickening_forall_mem_iff (coconePoints ι l t)
    (isSheaf_coconePoints ι hD hinj l t) (fun c : CoconeChart ι l t => c.V)
    (CoconeChart.exists_mem hsurj l t) (fun c => c.proj) (fun c => c.isThickening_proj hD)
    (fun c _ k => c.mem_coconePoints_iff hD hinj k)
  obtain ⟨k₀, hk₀⟩ := (hWG w).2 ⟨𝟙 _, Category.id_comp _⟩
  have := hw.1
  refine ⟨W, yoneda.map k₀, w, ?_, hw⟩
  refine IsPullback.of_forall_isPullback_app fun T' => ?_
  induction T' using Opposite.rec with
  | op T' =>
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext a
    change (coconeMap ι l).app (op T') (a ≫ k₀) = t.app (op T') (a ≫ w)
    exact app_map_eq_of_app_eq _ _ a.op hk₀
  · rintro (a₁ : T' ⟶ W) (a₂ : T' ⟶ W) ⟨-, h₂⟩
    exact (cancel_mono w).mp h₂
  · intro (x : T' ⟶ D.obj l) (y : T' ⟶ T) hxy
    obtain ⟨n, hn⟩ := (hWG y).1 ⟨x, hxy⟩
    refine ⟨n, injective_coconeMap_app ι hD hinj l T' ?_, hn⟩
    change (coconeMap ι l).app (op T') (n ≫ k₀) = (coconeMap ι l).app (op T') x
    exact (app_map_eq_of_app_eq _ _ n.op hk₀).trans
      ((congrArg (t.app (op T')) hn).trans hxy.symm)

/-! ### The kernels of the stages -/

include hsurj in
/-- **A point of `𝔛` over a quasi-compact scheme kills the kernel of some stage**: it lifts
Zariski locally to stages, finitely many of which suffice, and all of them map to a common later
stage. -/
theorem exists_kills_ker_coconeMap {S : Scheme.{u}} [CompactSpace S]
    (f : schemeToLTRSObj S ⟶ 𝔛.obj) :
    ∃ M : Λ, (ker (yonedaEquiv (coconeMap ι M)).hom).Kills f := by
  classical
  choose V m _ b hxV hb using fun x : S => exists_coconeMap_app_eq ι hsurj
    (show (mcQuillanFormalSchemePoints 𝔛).obj (op S) from ObjectProperty.homMk f) x
    (Classical.arbitrary Λ)
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set S))
    (fun x => (V x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
  obtain ⟨M, hM⟩ := Finset.exists_le (F.image m)
  refine ⟨M, kills_of_openCover _ f (fun x : F => V x) ?_ fun x => ?_⟩
  · refine iSup_eq_top_of_forall_exists_mem _ fun y => ?_
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.mp (hF (Set.mem_univ y))
    exact ⟨⟨x, hx⟩, hy⟩
  · have hle : m x ≤ M := hM _ (Finset.mem_image_of_mem _ x.2)
    have heq : schemeToLTRS.map (V x).ι ≫ f =
        schemeToLTRS.map (b x ≫ D.map (homOfLE hle)) ≫ (yonedaEquiv (coconeMap ι M)).hom := by
      rw [← app_hom_eq_schemeToLTRS_map_comp, coconeMap_app_comp_map, hb x]
      rfl
    rw [heq]
    exact (kills_ker _).comp _

include hsurj in
/-- **The kernels of the stages become small**: over a weak affine formal open `U`, every
neighbourhood of zero in `𝒪_𝔛(U)` contains the sections over `U` of the kernel of some stage.
Under a chart `U ≅ Spfw A` the neighbourhood contains the image of a weak ideal of definition `L`,
and the quotient point `Spec (A/L) → 𝔛` kills the kernel of some stage. -/
theorem exists_ker_coconeMap_subset {U : Opens 𝔛.obj} (hU : IsWeakAffineFormalOpen 𝔛.obj U)
    {N : Set (𝔛.obj.presheaf.obj (op U)).α} (hN : N ∈ nhds 0) :
    ∃ M : Λ, ((ker (yonedaEquiv (coconeMap ι M)).hom).ideal U : Set _) ⊆ N := by
  set e := weakChartSectionsHomeomorph _ hU.chart.admissible hU.chart.iso
  have he0 : e 0 = 0 := (weakChartSectionsRingEquiv _ hU.chart.admissible hU.chart.iso).map_zero
  have hN' : e ⁻¹' N ∈ nhds (0 : hU.chart.ring.α) :=
    e.continuous.continuousAt.preimage_mem_nhds (by rwa [he0])
  obtain ⟨L, hL, hLN⟩ :=
    (TopologicalRing.hasBasis_nhds_zero_isWeakIdealOfDefinition hU.chart.admissible).mem_iff.mp
      hN'
  obtain ⟨M, hM⟩ := exists_kills_ker_coconeMap ι hsurj
    (weakChartPoint _ hU.chart.admissible hU.chart.iso ⟨L, hL⟩)
  refine ⟨M, fun t ht => ?_⟩
  have h₀ := mem_ker_iff.mp (hM U ht)
  have he : (weakChartSections _ hU.chart.admissible hU.chart.iso).1 (e.symm t) = t :=
    e.apply_symm_apply t
  rw [← he] at h₀
  have hmem := hLN ((weakChartPoint_c_app_weakChartSections_eq_zero_iff _ hU.chart.admissible
    hU.chart.iso ⟨L, hL⟩ (e.symm t)).mp h₀)
  rwa [Set.mem_preimage, e.apply_symm_apply] at hmem

end Colimit

variable {𝔛 : McQuillanFormalScheme.{u}}

/-- **Stacks 0AIV, a colimit of schemes along thickenings gives a fundamental system.** If the
functor of points of a McQuillan formal scheme `𝔛` is a colimit of schemes `X_λ` along thickenings,
then the kernels of the morphisms `X_λ → 𝔛` form a nonempty directed fundamental system of weak
ideals of definition of `𝔛`, each cut out by its sections over the weak affine formal opens. -/
theorem exists_isFundamentalSystem_of_isColimitOfThickenings (h : 𝔛.IsColimitOfThickenings) :
    ∃ 𝒮 : Set (IdealSheaf 𝔛.obj), 𝒮.Nonempty ∧
      (∀ I ∈ 𝒮, ∀ J ∈ 𝒮, ∃ K ∈ 𝒮, ∀ W : Opens 𝔛.obj,
        K.ideal W ≤ I.ideal W ∧ K.ideal W ≤ J.ideal W) ∧
      (∀ I ∈ 𝒮, I.IsCutOutOn (IsWeakAffineFormalOpen 𝔛.obj)) ∧
      IsFundamentalSystemOfWeakIdealsOfDefinitionOn 𝒮 (IsWeakAffineFormalOpen 𝔛.obj) := by
  obtain ⟨Λ, _, _, _, D, hD, ι, hinj, hsurj⟩ := h
  have hthick := isThickening_presheaf_coconeMap ι hD hinj hsurj
  refine ⟨Set.range fun l => ker (yonedaEquiv (coconeMap ι l)).hom,
    ⟨_, Set.mem_range_self (Classical.arbitrary Λ)⟩, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨l₁, rfl⟩ _ ⟨l₂, rfl⟩
    obtain ⟨m, h₁, h₂⟩ := exists_ge_ge l₁ l₂
    exact ⟨_, ⟨m, rfl⟩, fun W => ⟨ker_coconeMap_le ι h₁ W, ker_coconeMap_le ι h₂ W⟩⟩
  · rintro _ ⟨l, rfl⟩
    exact isCutOutOn_ker_of_isThickening (hthick l)
  · rintro _ ⟨l, rfl⟩
    exact isWeakIdealOfDefinitionOn_ker_of_isThickening (hthick l)
  · intro U hU
    refine Filter.hasBasis_iff.mpr fun N => ⟨fun hN => ?_, ?_⟩
    · obtain ⟨M, hM⟩ := exists_ker_coconeMap_subset ι hsurj hU hN
      exact ⟨_, ⟨M, rfl⟩, hM⟩
    · rintro ⟨_, ⟨l, rfl⟩, hsub⟩
      exact Filter.mem_of_superset
        (((isWeakIdealOfDefinitionOn_ker_of_isThickening (hthick l)) U hU).1.mem_nhds
          (Ideal.zero_mem _)) hsub

end LocallyTopologicallyRingedSpace.IdealSheaf

end AlgebraicGeometry

end
