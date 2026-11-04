module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MorphismGlue
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.CanonicalRestriction

/-!
# Common refinement of the local descents of a morphism of modules, and their agreement on
overlaps

[Stacks Project, Tag 01ZR] (2) for a cofiltered diagram of quasi-compact quasi-separated schemes
is proved by Zariski glueing from the affine case.  Over an affine open `V` of a stage `D.obj i`
a morphism of the pullbacks of two finitely presented modules to the limit descends to some
stage over `i`, and this is taken here as a hypothesis. This file performs the two steps that
turn the local descents into glueing data:

* a **common refinement**: the finitely many stages produced for the members of a finite affine
  covering of `D.obj i` are refined to a single stage over `i`, at which every local descent is
  available simultaneously;
* **agreement on overlaps**: the local descents, restricted to the overlap of two members of the
  covering, agree at a further stage.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleLimits.IsStageDescent`: the descent condition relating a
  morphism of the pullbacks of two modules to the preimage of an open `V` of `D.obj i` in a
  stage over `i`, and the given morphism of the pullbacks to the limit. This is the conclusion
  of [Stacks Project, Tag 01ZR] (2) read over `V`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.isStageDescent_preimageStepHom`: the descent condition
  is inherited by the transport of a local descent to a later stage.
* `Stacks.AlgebraicGeometry.ModuleLimits.isStageDescent_preimageHomLE`: the descent condition is
  inherited by the restriction of a local descent to a smaller open.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_stage_descent_agree`: given the descent of a
  morphism over every affine open of a quasi-separated stage, a single stage over `i` carries a
  descent over every member of a finite family of affine opens, and any two of them agree over
  the overlap.

## Implementation notes

Every morphism in play is phrased as a pullback along a morphism *to the stage `D.obj i`*: for
an open `V` of `D.obj i` and `f : Y ⟶ D.obj i` the preimage `f ⁻¹ᵁ V` carries the morphism
`Stacks.AlgebraicGeometry.ModuleLimits.preimageHom f V`, the inclusion followed by `f`, and the
local objects are morphisms of the pullbacks of the two modules along it.  In that spelling the
three operations the argument needs are all instances of one construction,
`Stacks.AlgebraicGeometry.ModuleLimits.canStep`:

* restriction of a local morphism to a smaller open is `canStep` along
  `Stacks.AlgebraicGeometry.ModuleLimits.preimageLE`;
* transport of a local morphism to a later stage is `canStep` along
  `Stacks.AlgebraicGeometry.ModuleLimits.preimageRes`;
* restriction of the given morphism on the limit to an open of the limit is `canStep` along the
  inclusion of that open.

Consequently no `AlgebraicGeometry.Scheme.Modules.restrictFunctor` and no
`Stacks.AlgebraicGeometry.ModuleLimits.sqIso` appears, and the whole transport of the canonical
comparisons from `V` to `V ⊓ W` is formal: it is
`Stacks.AlgebraicGeometry.ModuleLimits.canonical_eq_of_further_step` for the stage side,
`Stacks.AlgebraicGeometry.ModuleLimits.canonical_eq_of_precomp` for the limit side, and
`Stacks.AlgebraicGeometry.ModuleLimits.canStep_canStep` to collapse the two restrictions of the
morphism on the limit into one. No statement here mentions the sections of a restriction, so
the identification `Γ(restrict M Z.ι, V) = Γ(M, Z.ι ''ᵁ V)`, which is `rfl` but not syntactic,
is never needed.

The two refinements are run in slice categories rather than in `I`: first in
`CategoryTheory.Over i`, to make the finitely many stages carrying the local descents refinable
to one, and then in `CategoryTheory.Over k` for the stage `k` so obtained, to make the finitely
many stages carrying the pairwise agreements refinable *compatibly*.  The second slice is what
the argument needs: a morphism of `CategoryTheory.Over k` records its composite with `k.hom`
through `CategoryTheory.Over.w`, so the transports of the local descents used for the different
pairs are transports along one and the same morphism, which they need not be if the refinement
is taken in `CategoryTheory.Over i`.

The index category is at the universe shape `{I : Type u} [Category.{u} I]` because the engine
of the agreement step, `Stacks.AlgebraicGeometry.ModuleLimits.exists_pullback_map_eq_of_isLimit`,
is applied to the diagram of preimages indexed by `CategoryTheory.Over i`, whose type of objects
must then be the universe of the schemes. This costs no generality: the restriction is removed
by `CategoryTheory.Functor.FullImage`.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe w v u

namespace Stacks.AlgebraicGeometry.ModuleLimits

/-! ### The preimage of an open under a morphism of schemes -/

section Preimage

variable {T Z Y X : Scheme.{u}}

/-- The structure morphism of the preimage of an open: for `f : Y ⟶ X` and an open `V` of `X`,
the inclusion of `f ⁻¹ᵁ V` into `Y` followed by `f`. -/
noncomputable def preimageHom (f : Y ⟶ X) (V : X.Opens) : (f ⁻¹ᵁ V).toScheme ⟶ X :=
  (f ⁻¹ᵁ V).ι ≫ f

/-- The restriction of `g` to the preimages of an open `V` of `X`, along a commuting triangle
`g ≫ f = h`.  For `g` a transition morphism of the diagram this is the transition morphism of
`AlgebraicGeometry.EventualLimit.preimageDiagram`, and for `g` a limit projection it is the
projection of `AlgebraicGeometry.EventualLimit.preimageCone`. -/
noncomputable def preimageRes (g : Z ⟶ Y) (f : Y ⟶ X) (h : Z ⟶ X) (hgf : g ≫ f = h)
    (V : X.Opens) : (h ⁻¹ᵁ V).toScheme ⟶ (f ⁻¹ᵁ V).toScheme :=
  g.resLE _ _ (by rw [← hgf, Scheme.Hom.comp_preimage])

/-- The inclusion of the preimage of a smaller open into the preimage of a larger one. -/
noncomputable def preimageLE (f : Y ⟶ X) {V W : X.Opens} (hVW : V ≤ W) :
    (f ⁻¹ᵁ V).toScheme ⟶ (f ⁻¹ᵁ W).toScheme :=
  Y.homOfLE (f.preimage_mono hVW)

/-- Restricting to the preimages and including are the two ways round the square cutting the
preimage of `V` out of the source of `g`. -/
@[reassoc (attr := simp)]
theorem preimageRes_comp_ι (g : Z ⟶ Y) (f : Y ⟶ X) (h : Z ⟶ X) (hgf : g ≫ f = h)
    (V : X.Opens) : preimageRes g f h hgf V ≫ (f ⁻¹ᵁ V).ι = (h ⁻¹ᵁ V).ι ≫ g :=
  Scheme.Hom.resLE_comp_ι g _

/-- The inclusion of the preimage of a smaller open, followed by the inclusion of the preimage
of a larger one, is the inclusion of the preimage of the smaller one. -/
@[reassoc (attr := simp)]
theorem preimageLE_comp_ι (f : Y ⟶ X) {V W : X.Opens} (hVW : V ≤ W) :
    preimageLE f hVW ≫ (f ⁻¹ᵁ W).ι = (f ⁻¹ᵁ V).ι :=
  Y.homOfLE_ι _

/-- The structure morphism of the preimage of `V` is cut out by the structure morphism of the
preimage of `V` one step up. -/
@[reassoc]
theorem preimageRes_comp_preimageHom (g : Z ⟶ Y) (f : Y ⟶ X) (h : Z ⟶ X) (hgf : g ≫ f = h)
    (V : X.Opens) : preimageRes g f h hgf V ≫ preimageHom f V = preimageHom h V := by
  rw [preimageHom, preimageRes_comp_ι_assoc, hgf, preimageHom]

/-- The structure morphism of the preimage of a smaller open factors through the structure
morphism of the preimage of a larger one. -/
@[reassoc]
theorem preimageLE_comp_preimageHom (f : Y ⟶ X) {V W : X.Opens} (hVW : V ≤ W) :
    preimageLE f hVW ≫ preimageHom f W = preimageHom f V := by
  rw [preimageHom, preimageLE_comp_ι_assoc, preimageHom]

/-- Restricting to the preimage of a smaller open and restricting along a commuting triangle
commute. -/
theorem preimageLE_comp_preimageRes (g : Z ⟶ Y) (f : Y ⟶ X) (h : Z ⟶ X) (hgf : g ≫ f = h)
    {V W : X.Opens} (hVW : V ≤ W) :
    preimageLE h hVW ≫ preimageRes g f h hgf W
      = preimageRes g f h hgf V ≫ preimageLE f hVW := by
  refine EventualLimit.hom_ext_opens ?_
  simp

/-- Two successive restrictions along commuting triangles are the restriction along the
composite triangle. -/
theorem preimageRes_comp_preimageRes (g' : T ⟶ Z) (g : Z ⟶ Y) (f : Y ⟶ X) (h : Z ⟶ X)
    (h' : T ⟶ X) (gg : T ⟶ Y) (hgf : g ≫ f = h) (hg' : g' ≫ h = h') (hgg : g' ≫ g = gg)
    (hgg' : gg ≫ f = h') (V : X.Opens) :
    preimageRes g' h h' hg' V ≫ preimageRes g f h hgf V = preimageRes gg f h' hgg' V := by
  refine EventualLimit.hom_ext_opens ?_
  rw [Category.assoc, preimageRes_comp_ι, preimageRes_comp_ι_assoc, preimageRes_comp_ι, hgg]

end Preimage

/-! ### Restriction and transport of a morphism of pullbacks over a preimage -/

section Step

variable {Z Y X : Scheme.{u}}

/-- The transport of a morphism of the pullbacks over the preimage of `V` along `f` to the
pullbacks over the preimage of `V` along `h`, for a commuting triangle `g ≫ f = h`. -/
noncomputable def preimageStepHom (g : Z ⟶ Y) (f : Y ⟶ X) (h : Z ⟶ X) (hgf : g ≫ f = h)
    (V : X.Opens) {F G : X.Modules}
    (ψ : (Scheme.Modules.pullback (preimageHom f V)).obj F ⟶
      (Scheme.Modules.pullback (preimageHom f V)).obj G) :
    (Scheme.Modules.pullback (preimageHom h V)).obj F ⟶
      (Scheme.Modules.pullback (preimageHom h V)).obj G :=
  canStep (preimageRes g f h hgf V) (preimageHom f V) (preimageHom h V)
    (preimageRes_comp_preimageHom g f h hgf V) ψ

/-- The restriction of a morphism of the pullbacks over the preimage of `W` to the pullbacks
over the preimage of a smaller open `V`. -/
noncomputable def preimageHomLE (f : Y ⟶ X) {V W : X.Opens} (hVW : V ≤ W)
    {F G : X.Modules}
    (ψ : (Scheme.Modules.pullback (preimageHom f W)).obj F ⟶
      (Scheme.Modules.pullback (preimageHom f W)).obj G) :
    (Scheme.Modules.pullback (preimageHom f V)).obj F ⟶
      (Scheme.Modules.pullback (preimageHom f V)).obj G :=
  canStep (preimageLE f hVW) (preimageHom f W) (preimageHom f V)
    (preimageLE_comp_preimageHom f hVW) ψ

/-- `Stacks.AlgebraicGeometry.ModuleLimits.canStep` depends on the morphism it is taken along
only through that morphism. -/
theorem canStep_congr_hom {Zk Zj Zi : Scheme.{u}} {m m' : Zk ⟶ Zj} (hm : m = m') (g : Zj ⟶ Zi)
    (mg : Zk ⟶ Zi) (hmg : m ≫ g = mg) (hmg' : m' ≫ g = mg) {F G : Zi.Modules}
    (ψ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G) :
    canStep m g mg hmg ψ = canStep m' g mg hmg' ψ := by
  subst hm; rfl

/-- `Stacks.AlgebraicGeometry.ModuleLimits.canStep` is determined by the pullback of the
morphism it is taken of. -/
theorem canStep_congr {Zk Zj Zi : Scheme.{u}} (m : Zk ⟶ Zj) (g : Zj ⟶ Zi) (mg : Zk ⟶ Zi)
    (hmg : m ≫ g = mg) {F G : Zi.Modules}
    {ψ ψ' : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G}
    (h : (Scheme.Modules.pullback m).map ψ = (Scheme.Modules.pullback m).map ψ') :
    canStep m g mg hmg ψ = canStep m g mg hmg ψ' := by
  rw [canStep, canStep, h]

/-- **Restricting to an overlap commutes with passing to a later stage.**  Restricting a
morphism of pullbacks to the preimage of a smaller open and then transporting it along a
commuting triangle is the same as transporting it first and restricting afterwards. -/
theorem preimageHomLE_preimageStepHom (g : Z ⟶ Y) (f : Y ⟶ X) (h : Z ⟶ X)
    (hgf : g ≫ f = h) {V W : X.Opens} (hVW : V ≤ W) {F G : X.Modules}
    (ψ : (Scheme.Modules.pullback (preimageHom f W)).obj F ⟶
      (Scheme.Modules.pullback (preimageHom f W)).obj G) :
    preimageHomLE h hVW (preimageStepHom g f h hgf W ψ)
      = preimageStepHom g f h hgf V (preimageHomLE f hVW ψ) := by
  rw [preimageHomLE, preimageStepHom,
    canStep_canStep (preimageLE h hVW) (preimageRes g f h hgf W) (preimageHom f W)
      (preimageLE h hVW ≫ preimageRes g f h hgf W) (preimageHom h W) (preimageHom h V) rfl
      (preimageRes_comp_preimageHom g f h hgf W) (preimageLE_comp_preimageHom h hVW)
      (by rw [Category.assoc, preimageRes_comp_preimageHom, preimageLE_comp_preimageHom]),
    preimageStepHom, preimageHomLE,
    canStep_canStep (preimageRes g f h hgf V) (preimageLE f hVW) (preimageHom f W)
      (preimageRes g f h hgf V ≫ preimageLE f hVW) (preimageHom f V) (preimageHom h V) rfl
      (preimageLE_comp_preimageHom f hVW) (preimageRes_comp_preimageHom g f h hgf V)
      (by rw [Category.assoc, preimageLE_comp_preimageHom, preimageRes_comp_preimageHom])]
  exact canStep_congr_hom (preimageLE_comp_preimageRes g f h hgf hVW) _ _ _ _ ψ

end Step

/-! ### Transporting the canonical comparison along a further morphism on the limit side -/

/-- If a morphism `ψ` between pullbacks along `g` is carried by the canonical comparison to a
morphism `χ` between pullbacks along `π`, then it is carried to the morphism obtained from `χ` by
pulling back along a further morphism `n` into the source of `π`. This is dual to
`Stacks.AlgebraicGeometry.ModuleLimits.canonical_eq_of_further_step`. -/
theorem canonical_eq_of_precomp {L' L W X : Scheme.{u}} (n : L' ⟶ L) (p : L ⟶ W) (p' : L' ⟶ W)
    (hp : n ≫ p = p') (g : W ⟶ X) (π : L ⟶ X) (hπ : p ≫ g = π) (π' : L' ⟶ X)
    (hπ' : p' ≫ g = π') (hnπ : n ≫ π = π') {F G : X.Modules}
    (ψ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback g).obj G)
    (χ : (Scheme.Modules.pullback π).obj F ⟶ (Scheme.Modules.pullback π).obj G)
    (h : (Scheme.Modules.pullback p).map ψ ≫ canHom p g π hπ G = canHom p g π hπ F ≫ χ) :
    (Scheme.Modules.pullback p').map ψ ≫ canHom p' g π' hπ' G
      = canHom p' g π' hπ' F ≫ canStep n π π' hnπ χ := by
  rw [← cancel_epi (canHom n p p' hp ((Scheme.Modules.pullback g).obj F)),
    ← canHom_naturality_assoc n p p' hp ψ,
    ← canHom_comp n p g p' π π' hp hπ hπ' hnπ G, ← Functor.map_comp_assoc, h,
    Functor.map_comp, Category.assoc, ← canHom_comp_canStep n π π' hnπ χ,
    canHom_comp_assoc n p g p' π π' hp hπ hπ' hnπ F]

/-! ### The descent condition over an open of a stage -/

section Descent

variable {I : Type v} [Category.{w} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- The restriction of the limit projection `c.π.app j` to the preimages of an open `V` of the
stage `D.obj i`, along a morphism `e : j ⟶ i`.  This is the projection of
`AlgebraicGeometry.EventualLimit.preimageCone`. -/
noncomputable def coneRes {i j : I} (e : j ⟶ i) (V : (D.obj i).Opens) :
    (c.π.app i ⁻¹ᵁ V).toScheme ⟶ (D.map e ⁻¹ᵁ V).toScheme :=
  preimageRes (c.π.app j) (D.map e) (c.π.app i) (c.w e) V

/-- The structure morphism of the preimage of `V` in the vertex of the cone factors through the
structure morphism of the preimage of `V` in the stage. -/
@[reassoc]
theorem coneRes_comp_preimageHom {i j : I} (e : j ⟶ i) (V : (D.obj i).Opens) :
    coneRes D c e V ≫ preimageHom (D.map e) V = preimageHom (c.π.app i) V :=
  preimageRes_comp_preimageHom _ _ _ _ V

/-- The restriction to the preimage of an open `V` of the stage `D.obj i` of a morphism of the
pullbacks of two modules to the vertex of the cone.  It is
`Stacks.AlgebraicGeometry.ModuleLimits.canStep` along the inclusion of `c.π.app i ⁻¹ᵁ V`. -/
noncomputable def limitRestrictHom {i : I} {F G : (D.obj i).Modules}
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G) (V : (D.obj i).Opens) :
    (Scheme.Modules.pullback (preimageHom (c.π.app i) V)).obj F ⟶
      (Scheme.Modules.pullback (preimageHom (c.π.app i) V)).obj G :=
  canStep (c.π.app i ⁻¹ᵁ V).ι (c.π.app i) (preimageHom (c.π.app i) V) rfl φ

/-- **The descent condition of [Stacks Project, Tag 01ZR] (2) over an open of a stage.**  A
morphism `ψ` of the pullbacks of `F` and `G` to the preimage of an open `V` of `D.obj i` in the
stage `D.obj j`, for `e : j ⟶ i`, *descends* the morphism `φ` of the pullbacks to the vertex of
the cone over `V` when its own pullback to the preimage of `V` in the vertex is, through the
canonical comparison `Stacks.AlgebraicGeometry.ModuleLimits.canHom`, the restriction
`limitRestrictHom` of `φ` to that preimage. -/
def IsStageDescent {i j : I} (e : j ⟶ i) {F G : (D.obj i).Modules}
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G) (V : (D.obj i).Opens)
    (ψ : (Scheme.Modules.pullback (preimageHom (D.map e) V)).obj F ⟶
      (Scheme.Modules.pullback (preimageHom (D.map e) V)).obj G) : Prop :=
  (Scheme.Modules.pullback (coneRes D c e V)).map ψ ≫
      canHom (coneRes D c e V) (preimageHom (D.map e) V) (preimageHom (c.π.app i) V)
        (coneRes_comp_preimageHom D c e V) G
    = canHom (coneRes D c e V) (preimageHom (D.map e) V) (preimageHom (c.π.app i) V)
        (coneRes_comp_preimageHom D c e V) F ≫ limitRestrictHom D c φ V

/-- **The descent condition passes to a later stage.**  If `ψ` descends `φ` over `V` at the
stage `e : j ⟶ i`, then the transport of `ψ` along a further morphism `f : k ⟶ j` descends `φ`
over `V` at the stage `f ≫ e`. -/
theorem isStageDescent_preimageStepHom {i j k : I} (e : j ⟶ i) (f : k ⟶ j) (e' : k ⟶ i)
    (hf : f ≫ e = e') {F G : (D.obj i).Modules}
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G) (V : (D.obj i).Opens)
    (ψ : (Scheme.Modules.pullback (preimageHom (D.map e) V)).obj F ⟶
      (Scheme.Modules.pullback (preimageHom (D.map e) V)).obj G)
    (h : IsStageDescent D c e φ V ψ) :
    IsStageDescent D c e' φ V
      (preimageStepHom (D.map f) (D.map e) (D.map e') (by rw [← hf, D.map_comp]) V ψ) := by
  have hm : coneRes D c e' V ≫ preimageRes (D.map f) (D.map e) (D.map e')
      (by rw [← hf, D.map_comp]) V = coneRes D c e V :=
    preimageRes_comp_preimageRes (c.π.app k) (D.map f) (D.map e) (D.map e') (c.π.app i)
      (c.π.app j) _ (c.w e') (c.w f) (c.w e) V
  exact canonical_eq_of_further_step (coneRes D c e' V) _ (coneRes D c e V) hm
    (preimageHom (D.map e) V) (preimageHom (c.π.app i) V) (coneRes_comp_preimageHom D c e V)
    (preimageHom (D.map e') V) (preimageRes_comp_preimageHom _ _ _ _ V)
    (coneRes_comp_preimageHom D c e' V) ψ (limitRestrictHom D c φ V) h

/-- **The descent condition passes to a smaller open.**  If `ψ` descends `φ` over `W` at the
stage `e : j ⟶ i`, then the restriction of `ψ` to the preimage of a smaller open `V` descends
`φ` over `V` at the same stage. -/
theorem isStageDescent_preimageHomLE {i j : I} (e : j ⟶ i) {F G : (D.obj i).Modules}
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G) {V W : (D.obj i).Opens} (hVW : V ≤ W)
    (ψ : (Scheme.Modules.pullback (preimageHom (D.map e) W)).obj F ⟶
      (Scheme.Modules.pullback (preimageHom (D.map e) W)).obj G)
    (h : IsStageDescent D c e φ W ψ) :
    IsStageDescent D c e φ V (preimageHomLE (D.map e) hVW ψ) := by
  have hπ' : (preimageLE (c.π.app i) hVW ≫ coneRes D c e W) ≫ preimageHom (D.map e) W
      = preimageHom (c.π.app i) V := by
    rw [Category.assoc, coneRes_comp_preimageHom, preimageLE_comp_preimageHom]
  have key := canonical_eq_of_precomp (preimageLE (c.π.app i) hVW) (coneRes D c e W)
    (preimageLE (c.π.app i) hVW ≫ coneRes D c e W) rfl (preimageHom (D.map e) W)
    (preimageHom (c.π.app i) W) (coneRes_comp_preimageHom D c e W) (preimageHom (c.π.app i) V)
    hπ' (preimageLE_comp_preimageHom (c.π.app i) hVW) ψ (limitRestrictHom D c φ W) h
  rw [limitRestrictHom, canStep_canStep (preimageLE (c.π.app i) hVW) (c.π.app i ⁻¹ᵁ W).ι
    (c.π.app i) (c.π.app i ⁻¹ᵁ V).ι (preimageHom (c.π.app i) W) (preimageHom (c.π.app i) V)
    (preimageLE_comp_ι (c.π.app i) hVW) rfl (preimageLE_comp_preimageHom (c.π.app i) hVW)
    rfl] at key
  have hm : coneRes D c e V ≫ preimageLE (D.map e) hVW
      = preimageLE (c.π.app i) hVW ≫ coneRes D c e W :=
    (preimageLE_comp_preimageRes (c.π.app j) (D.map e) (c.π.app i) (c.w e) hVW).symm
  exact canonical_eq_of_further_step (coneRes D c e V) (preimageLE (D.map e) hVW)
    (preimageLE (c.π.app i) hVW ≫ coneRes D c e W) hm (preimageHom (D.map e) W)
    (preimageHom (c.π.app i) V) hπ' (preimageHom (D.map e) V)
    (preimageLE_comp_preimageHom (D.map e) hVW) (coneRes_comp_preimageHom D c e V) ψ
    (limitRestrictHom D c φ V) key

/-! ### The diagram and the cone of preimages, in the present spelling -/

/-- The projection of `AlgebraicGeometry.EventualLimit.preimageCone` is the restriction of the
limit projection to the preimages. -/
theorem preimageCone_π_app_eq {i : I} (U : (D.obj i).Opens) (k : Over i) :
    (EventualLimit.preimageCone D c i U).π.app k = coneRes D c k.hom U := rfl

/-- The transition morphism of `AlgebraicGeometry.EventualLimit.preimageDiagram` is the
restriction of the transition morphism of the diagram to the preimages. -/
theorem preimageDiagram_map_eq {i : I} (U : (D.obj i).Opens) {x y : Over i} (g : x ⟶ y) :
    (EventualLimit.preimageDiagram D i U).map g
      = preimageRes (D.map g.left) (D.map y.hom) (D.map x.hom)
        (by rw [← D.map_comp, Over.w g]) U := rfl

end Descent

/-! ### Agreement of two local descents over an overlap -/

section Agree

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D)

/-- Two local descents of `φ`, over opens `W₁` and `W₂` of a stage `D.obj i` and at the same
stage `k` over `i`, agree over the overlap `W₁ ⊓ W₂` at some stage over `k` — and then at every
stage over that one. -/
private theorem exists_over_preimageHomLE_eq (hc : IsLimit c) {i : I}
    {F G : (D.obj i).Modules} [F.IsFinitePresentation] [G.IsFinitePresentation]
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G) (k : Over i) (W₁ W₂ : (D.obj i).Opens)
    (hW : IsCompact ((W₁ ⊓ W₂ : (D.obj i).Opens) : Set (D.obj i)))
    (ψ₁ : (Scheme.Modules.pullback (preimageHom (D.map k.hom) W₁)).obj F ⟶
      (Scheme.Modules.pullback (preimageHom (D.map k.hom) W₁)).obj G)
    (ψ₂ : (Scheme.Modules.pullback (preimageHom (D.map k.hom) W₂)).obj F ⟶
      (Scheme.Modules.pullback (preimageHom (D.map k.hom) W₂)).obj G)
    (h₁ : IsStageDescent D c k.hom φ W₁ ψ₁) (h₂ : IsStageDescent D c k.hom φ W₂ ψ₂) :
    ∃ x : Over k, ∀ (y : Over k), (y ⟶ x) →
      preimageHomLE (D.map y.left.hom) (show W₁ ⊓ W₂ ≤ W₁ from inf_le_left)
          (preimageStepHom (D.map y.hom.left) (D.map k.hom) (D.map y.left.hom)
            (by rw [← D.map_comp, Over.w y.hom]) W₁ ψ₁)
        = preimageHomLE (D.map y.left.hom) (show W₁ ⊓ W₂ ≤ W₂ from inf_le_right)
          (preimageStepHom (D.map y.hom.left) (D.map k.hom) (D.map y.left.hom)
            (by rw [← D.map_comp, Over.w y.hom]) W₂ ψ₂) := by
  set U : (D.obj i).Opens := W₁ ⊓ W₂ with hUdef
  set r₁ := preimageHomLE (D.map k.hom) (show U ≤ W₁ from inf_le_left) ψ₁ with hr₁def
  set r₂ := preimageHomLE (D.map k.hom) (show U ≤ W₂ from inf_le_right) ψ₂ with hr₂def
  have hr₁ : IsStageDescent D c k.hom φ U r₁ :=
    isStageDescent_preimageHomLE D c k.hom φ (show U ≤ W₁ from inf_le_left) ψ₁ h₁
  have hr₂ : IsStageDescent D c k.hom φ U r₂ :=
    isStageDescent_preimageHomLE D c k.hom φ (show U ≤ W₂ from inf_le_right) ψ₂ h₂
  have hpull : (Scheme.Modules.pullback (coneRes D c k.hom U)).map r₁
      = (Scheme.Modules.pullback (coneRes D c k.hom U)).map r₂ := by
    refine (cancel_mono (canHom (coneRes D c k.hom U) (preimageHom (D.map k.hom) U)
      (preimageHom (c.π.app i) U) (coneRes_comp_preimageHom D c k.hom U) G)).mp ?_
    exact Eq.trans hr₁ (Eq.symm hr₂)
  have hFfp :
      ((Scheme.Modules.pullback (preimageHom (D.map k.hom) U)).obj F).IsFinitePresentation :=
    isFinitePresentation_pullback _ F
  have hGfp :
      ((Scheme.Modules.pullback (preimageHom (D.map k.hom) U)).obj G).IsFinitePresentation :=
    isFinitePresentation_pullback _ G
  have haff : ∀ {x y : Over i} (g : x ⟶ y),
      IsAffineHom ((EventualLimit.preimageDiagram D i U).map g) := fun {_ _} g =>
    EventualLimit.preimageDiagram_isAffineHom D i U g
  have hcs : CompactSpace ((EventualLimit.preimageDiagram D i U).obj k) :=
    isCompact_iff_compactSpace.mp ((D.map k.hom).isCompact_preimage hW)
  obtain ⟨x, e, hxe⟩ := @exists_pullback_map_eq_of_isLimit (Over i) _ _
    (EventualLimit.preimageDiagram D i U) haff (EventualLimit.preimageCone D c i U)
    (EventualLimit.isLimitPreimageCone D c hc i U) k hcs _ _ hFfp hGfp r₁ r₂
    (by rw [preimageCone_π_app_eq]; exact hpull)
  refine ⟨Over.mk e, fun y m => ?_⟩
  have hw : y.hom.left ≫ k.hom = y.left.hom := Over.w y.hom
  have hstep : (Scheme.Modules.pullback
        ((EventualLimit.preimageDiagram D i U).map y.hom)).map r₁
      = (Scheme.Modules.pullback ((EventualLimit.preimageDiagram D i U).map y.hom)).map r₂ := by
    have hm : m.left ≫ e = y.hom := Over.w m
    rw [← hm, Functor.map_comp]
    exact pullback_map_eq_of_precomp _ _ hxe
  rw [preimageHomLE_preimageStepHom, preimageHomLE_preimageStepHom, ← hr₁def, ← hr₂def,
    preimageStepHom, preimageStepHom]
  exact canStep_congr _ _ _ _ hstep

/-! ### The common refinement and the overlap agreement -/

/-- In a cofiltered category, a finite family of objects has a common refinement. -/
private theorem exists_forall_nonempty_hom {J : Type*} [Category J] [IsCofiltered J]
    {ι : Type*} [Finite ι] (f : ι → J) : ∃ k, Nonempty (∀ a, k ⟶ f a) := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image f)
  exact ⟨k, ⟨fun a => (hk (Finset.mem_image_of_mem _ (Finset.mem_univ a))).some⟩⟩

/-- Let `c` be a limit cone on a cofiltered diagram `D` of schemes with affine transition
morphisms, let `D.obj i` be a quasi-separated stage, let `F` and `G` be sheaves of modules of
finite presentation on `D.obj i` and let `φ` be a morphism of their pullbacks to the vertex of
the cone.  Suppose `φ` descends over every affine open of `D.obj i`,
at some stage over `i` depending on the open.  Then for any finite family `V` of affine opens of
`D.obj i` there are a single stage `k` over `i` and a morphism over each `V a` at that stage
descending `φ`, such that any two of them agree over the overlap `V a ⊓ V b`.

The family is not required to cover `D.obj i`. -/
theorem exists_stage_descent_agree (hc : IsLimit c) (i : I) [QuasiSeparatedSpace (D.obj i)]
    (F G : (D.obj i).Modules) [F.IsFinitePresentation] [G.IsFinitePresentation]
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G)
    {ι : Type*} [Finite ι] (V : ι → (D.obj i).Opens) (hV : ∀ a, IsAffineOpen (V a))
    (hloc : ∀ W : (D.obj i).Opens, IsAffineOpen W →
      ∃ (j : I) (e : j ⟶ i)
        (ψ : (Scheme.Modules.pullback (preimageHom (D.map e) W)).obj F ⟶
          (Scheme.Modules.pullback (preimageHom (D.map e) W)).obj G),
        IsStageDescent D c e φ W ψ) :
    ∃ (k : I) (e : k ⟶ i)
      (ψ : ∀ a, (Scheme.Modules.pullback (preimageHom (D.map e) (V a))).obj F ⟶
        (Scheme.Modules.pullback (preimageHom (D.map e) (V a))).obj G),
      (∀ a, IsStageDescent D c e φ (V a) (ψ a)) ∧
      ∀ a b, preimageHomLE (D.map e) (show V a ⊓ V b ≤ V a from inf_le_left) (ψ a)
        = preimageHomLE (D.map e) (show V a ⊓ V b ≤ V b from inf_le_right) (ψ b) := by
  have hcpt : ∀ a b : ι, IsCompact ((V a ⊓ V b : (D.obj i).Opens) : Set (D.obj i)) := by
    intro a b
    have h := QuasiSeparatedSpace.inter_isCompact (α := D.obj i) (V a) (V b)
      (V a).isOpen (hV a).isCompact (V b).isOpen (hV b).isCompact
    simpa using h
  choose jj ee ψ₀ hψ₀ using fun a => hloc (V a) (hV a)
  obtain ⟨k, ⟨hkm⟩⟩ := exists_forall_nonempty_hom fun a => Over.mk (ee a)
  have hkw : ∀ a, (hkm a).left ≫ ee a = k.hom := fun a => Over.w (hkm a)
  set ψ₁ : ∀ a, (Scheme.Modules.pullback (preimageHom (D.map k.hom) (V a))).obj F ⟶
      (Scheme.Modules.pullback (preimageHom (D.map k.hom) (V a))).obj G := fun a =>
    preimageStepHom (D.map (hkm a).left) (D.map (ee a)) (D.map k.hom)
      (by rw [← D.map_comp, hkw a]) (V a) (ψ₀ a) with hψ₁def
  have hψ₁ : ∀ a, IsStageDescent D c k.hom φ (V a) (ψ₁ a) := fun a =>
    isStageDescent_preimageStepHom D c (ee a) (hkm a).left k.hom (hkw a) φ (V a) (ψ₀ a) (hψ₀ a)
  choose xx hxx using fun p : ι × ι =>
    exists_over_preimageHomLE_eq D c hc φ k (V p.1) (V p.2) (hcpt p.1 p.2) (ψ₁ p.1) (ψ₁ p.2)
      (hψ₁ p.1) (hψ₁ p.2)
  obtain ⟨z, ⟨hzm⟩⟩ := exists_forall_nonempty_hom xx
  have hzw : z.hom.left ≫ k.hom = z.left.hom := Over.w z.hom
  refine ⟨z.left.left, z.left.hom, fun a => preimageStepHom (D.map z.hom.left) (D.map k.hom)
    (D.map z.left.hom) (by rw [← D.map_comp, hzw]) (V a) (ψ₁ a), fun a => ?_, fun a b => ?_⟩
  · exact isStageDescent_preimageStepHom D c k.hom z.hom.left z.left.hom hzw φ (V a) (ψ₁ a)
      (hψ₁ a)
  · exact hxx (a, b) z (hzm (a, b))

end Agree

end Stacks.AlgebraicGeometry.ModuleLimits

end
