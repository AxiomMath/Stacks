module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.ClopenLift.ClopenSection
public import StacksFrontier.AlgebraicGeometry.Curves.PointFixingAutFinOrder
public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.Restrict
public import StacksFrontier.AlgebraicGeometry.Variety.Automorphisms.IntegralCurveReduction
public import StacksFrontier.AlgebraicGeometry.Variety.Automorphisms.ModulePullback

/-!
# Automorphisms inducing the identity on the underlying space, over an arbitrary field

Let `X` be a reduced scheme locally of finite type over a field `k` and let `f : X → X` be an
**automorphism** over `k` which fixes every point of the underlying topological space. If every
irreducible component of `X` has positive dimension then `f` is the identity, and — for `X` of
finite type — every `𝒪_X`-module is isomorphic to its pullback along `f`. These are the two
clauses of [Stacks, Tag 0G05], over an arbitrary field and with nothing carried.

The hypothesis that `f` is an automorphism is necessary, and is where this statement differs from
`AlgebraicGeometry.eq_id_of_eq_on_points`, which is about endomorphisms and therefore has to
carry a hypothesis on the base field: over a finite field the `p`-power Frobenius of the affine
line is an endomorphism fixing every point which is not the identity,
`AlgHom.exists_comap_eq_ne_id_of_finite_field`.

## Main results

* `AlgebraicGeometry.eq_id_of_isIso_of_eq_on_points`: **clause (2) of [Stacks, Tag 0G05]**.
* `AlgebraicGeometry.exists_iso_pullback_of_isIso_of_eq_on_points_of_connectedSpace`: clause (1)
  of the tag for a connected scheme, over an arbitrary field.
* `AlgebraicGeometry.exists_iso_pullback_of_isIso_of_eq_on_points`: **clause (1) of
  [Stacks, Tag 0G05]**, for an arbitrary reduced scheme of finite type over `k`.

## Implementation notes

The proof is the source's. Over an infinite field it is the density of the rational points of the
affine line, which is `AlgebraicGeometry.eq_id_of_eq_on_points`; over a finite field the source
reduces to curves and uses that a curve over a finite field has a finite automorphism group. That
reduction is `AlgebraicGeometry.eq_id_of_affine_curve_restrictions`, and the curve case is
`AlgebraicGeometry.eq_id_of_eq_on_points_of_isCurve`, whose finite-field half rests on the finite
order of a point-fixing automorphism of a curve,
`AlgebraicGeometry.isOfFinOrder_curveAut_of_fixes_points`. Both halves are covered by the curve
case, so the field is not split on here.

Finite type over the field is `LocallyOfFiniteType` alone in clause (2): quasi-compactness of the
structure morphism is not used there, so that statement is slightly more general than the
source's. Clause (1) does use it, through the finiteness of the set of connected components.

Clause (1) is assembled from the connected case over the connected components, which are clopen
and finite in number on a Noetherian space: the restriction of the pullback to a component is the
pullback of the restriction, `AlgebraicGeometry.restrictPullbackIso`, and the component
isomorphisms glue because distinct components meet in `⊥`, where the sections of a sheaf are a
subsingleton, so the overlap condition of
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover` is free. That the
glued morphism is an isomorphism is
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict`.

## References

* [Stacks Project, Tag 0G05](https://stacks.math.columbia.edu/tag/0G05)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0G05, clause (2).** Let `X` be a reduced scheme locally of finite type
over a field `k` and let `f : X ⟶ X` be an automorphism over `k` which induces the identity map
on the underlying topological space of `X`. If every irreducible component of `X` has positive
dimension then `f` is the identity.

Nothing is carried and no hypothesis is put on `k`. The source's two cases are both handled by
the curve case `AlgebraicGeometry.eq_id_of_eq_on_points_of_isCurve`, to which
`AlgebraicGeometry.eq_id_of_affine_curve_restrictions` reduces the statement: an integral affine
curve over `k` is a curve in the sense of `AlgebraicGeometry.IsCurve`, being integral, separated
and of finite type over `k` of dimension one. -/
@[stacks 0G05 "clause (2) in full: an automorphism over `k` of a reduced scheme locally of finite \
type over `k` fixing every point of the underlying space is the identity when every irreducible \
component has positive dimension. No hypothesis on the base field and nothing carried. The \
automorphism hypothesis is necessary — for an endomorphism the statement fails over a finite \
field, by `AlgHom.exists_comap_eq_ne_id_of_finite_field` — which is why this stands beside \
`AlgebraicGeometry.eq_id_of_eq_on_points`, the endomorphism statement with the base field in a \
disjunctive hypothesis"]
theorem eq_id_of_isIso_of_eq_on_points {k : Type u} [Field k] {X : Scheme.{u}} [IsReduced X]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (f : X ⟶ X) [IsIso f] (hf : f ≫ p = p)
    (hpoints : ∀ x : X, f x = x)
    (hdim : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z) :
    f = 𝟙 X := by
  refine eq_id_of_affine_curve_restrictions p f hf hpoints hdim ?_
  intro C _ _ q _ g _ hg hgpoints hdimC
  let _ : IsVariety k q := { }
  let _ : IsCurve k q := { topologicalKrullDim_eq_one := hdimC }
  exact eq_id_of_eq_on_points_of_isCurve q g hg hgpoints

/-- A scheme with a quasi-compact, locally finite type map to the spectrum of a field has a
Noetherian underlying space. -/
private theorem noetherianSpace_of_quasiCompact {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p] :
    TopologicalSpace.NoetherianSpace X := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  exact noetherianSpace_of_isLocallyNoetherianSpace X
    (isLocallyNoetherianSpace_of_isLocallyNoetherian X)

/-- **Clause (1) of [Stacks, Tag 0G05] for a connected scheme**, over an arbitrary field: every
module on a connected reduced scheme of finite type over `k` is isomorphic to its pullback along
a `k`-automorphism which fixes every point of the underlying topological space.

This drops the hypothesis `Infinite k` of
`AlgebraicGeometry.exists_iso_pullback_of_eq_on_points_of_connectedSpace`, at the cost of asking
that the endomorphism be an automorphism — which is what the tag asks for anyway, and what makes
the positive-dimensional case unconditional, by `AlgebraicGeometry.eq_id_of_isIso_of_eq_on_points`
above. The other case of a connected scheme is a one-point scheme, the spectrum of a finite
extension of `k`, where the automorphism may be nontrivial and a module is isomorphic to its
twist only through a basis. Coherence is not needed.

Connectedness is still carried: assembling the general case needs isomorphisms of modules to be
glued over the pairwise disjoint open connected components. -/
theorem exists_iso_pullback_of_isIso_of_eq_on_points_of_connectedSpace {k : Type u} [Field k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p] [IsReduced X]
    [ConnectedSpace X] (f : X ⟶ X) [IsIso f] (hf : f ≫ p = p) (hpoints : ∀ x : X, f x = x)
    (F : X.Modules) :
    Nonempty ((Scheme.Modules.pullback f).obj F ≅ F) := by
  let _ : TopologicalSpace.NoetherianSpace X := noetherianSpace_of_quasiCompact p
  let _ : Nonempty X := ConnectedSpace.toNonempty
  rcases subsingleton_or_irreducibleComponents_positive X with hsingle | hpositive
  · let _ : Subsingleton X := hsingle
    exact exists_iso_pullback_of_subsingleton f F
  · have hfid := eq_id_of_isIso_of_eq_on_points p f hf hpoints fun Z hZ ↦ hpositive ⟨Z, hZ⟩
    exact ⟨(Scheme.Modules.pullbackCongr hfid).app _ ≪≫ (Scheme.Modules.pullbackId X).app _⟩

/-! ### Clause (1) in general: gluing over the connected components -/

/-- A connected component of a scheme with finitely many of them, as a clopen open subscheme. -/
private noncomputable def connectedComponentOpen {X : Scheme.{u}}
    [Finite (_root_.ConnectedComponents X)] (c : _root_.ConnectedComponents X) : X.Opens :=
  ⟨connectedComponent c.out,
    (TopologicalSpace.isClopen_connectedComponent_of_finite_connectedComponents c.out).2⟩

private lemma mem_connectedComponentOpen {X : Scheme.{u}} [Finite (_root_.ConnectedComponents X)]
    (x : X) : x ∈ connectedComponentOpen (_root_.ConnectedComponents.mk x) :=
  _root_.ConnectedComponents.coe_eq_coe'.mp (Quotient.out_eq _).symm

private lemma mk_eq_of_mem_connectedComponentOpen {X : Scheme.{u}}
    [Finite (_root_.ConnectedComponents X)] {c : _root_.ConnectedComponents X} {x : X}
    (hx : x ∈ connectedComponentOpen c) : _root_.ConnectedComponents.mk x = c :=
  (_root_.ConnectedComponents.coe_eq_coe'.mpr hx).trans (Quotient.out_eq c)

private lemma isOpenCover_connectedComponentOpen (X : Scheme.{u})
    [Finite (_root_.ConnectedComponents X)] :
    TopologicalSpace.IsOpenCover (connectedComponentOpen (X := X)) := by
  refine eq_top_iff.mpr fun x _ ↦ ?_
  exact TopologicalSpace.Opens.mem_iSup.mpr
    ⟨_root_.ConnectedComponents.mk x, mem_connectedComponentOpen x⟩

private lemma le_bot_of_le_connectedComponentOpen {X : Scheme.{u}}
    [Finite (_root_.ConnectedComponents X)] {c c' : _root_.ConnectedComponents X} (h : c ≠ c')
    {V : X.Opens} (h₁ : V ≤ connectedComponentOpen c) (h₂ : V ≤ connectedComponentOpen c') :
    V = ⊥ := by
  refine eq_bot_iff.mpr fun x hx ↦ ?_
  exact absurd ((mk_eq_of_mem_connectedComponentOpen (h₁ hx)).symm.trans
    (mk_eq_of_mem_connectedComponentOpen (h₂ hx))) h

/-- For an open subscheme preserved by a point-fixing endomorphism, the restriction of a pullback
is the pullback of the restriction along the restricted endomorphism. -/
noncomputable def restrictPullbackIso {X : Scheme.{u}} (f : X ⟶ X)
    (hpoints : ∀ x : X, f x = x) (U : X.Opens) (F : X.Modules) :
    ((Scheme.Modules.pullback f).obj F).restrict U.ι ≅
      (Scheme.Modules.pullback (f.resLE U U (preimage_eq_of_apply_eq f hpoints U).ge)).obj
        (F.restrict U.ι) :=
  (Scheme.Modules.restrictFunctorIsoPullback U.ι).app ((Scheme.Modules.pullback f).obj F) ≪≫
    (Scheme.Modules.pullbackComp U.ι f).app F ≪≫
    (Scheme.Modules.pullbackCongr
      (Scheme.Hom.resLE_comp_ι f (preimage_eq_of_apply_eq f hpoints U).ge).symm).app F ≪≫
    ((Scheme.Modules.pullbackComp
      (f.resLE U U (preimage_eq_of_apply_eq f hpoints U).ge) U.ι).app F).symm ≪≫
    (Scheme.Modules.pullback
      (f.resLE U U (preimage_eq_of_apply_eq f hpoints U).ge)).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app F).symm

private lemma le_of_ι_image_eq {X : Scheme.{u}} {U : X.Opens} {W : U.toScheme.Opens}
    {V : X.Opens} (h : U.ι ''ᵁ W = V) : V ≤ U := by
  intro x hx
  rw [← h] at hx
  obtain ⟨y, -, rfl⟩ := hx
  exact y.2

private lemma exists_iso_restrict_connectedComponentOpen {k : Type u} [Field k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [IsReduced X]
    [CompactSpace X] [Finite (_root_.ConnectedComponents X)] (f : X ⟶ X) [IsIso f]
    (hf : f ≫ p = p) (hpoints : ∀ x : X, f x = x) (F : X.Modules)
    (c : _root_.ConnectedComponents X) :
    Nonempty (((Scheme.Modules.pullback f).obj F).restrict (connectedComponentOpen c).ι ≅
      F.restrict (connectedComponentOpen c).ι) := by
  set U : X.Opens := connectedComponentOpen c
  let _ : IsReduced U.toScheme := isReduced_of_isOpenImmersion U.ι
  let _ : ConnectedSpace U.toScheme :=
    isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  let _ : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp
    ((TopologicalSpace.isClopen_connectedComponent_of_finite_connectedComponents
      (Quotient.out c)).1.isCompact)
  let _ : QuasiCompact (U.ι ≫ p) := quasiCompact_of_compactSpace _
  let _ : IsIso (f.resLE U U (preimage_eq_of_apply_eq f hpoints U).ge) :=
    isIso_resLE_of_apply_eq f hpoints U
  obtain ⟨β⟩ := exists_iso_pullback_of_isIso_of_eq_on_points_of_connectedSpace (U.ι ≫ p)
    (f.resLE U U (preimage_eq_of_apply_eq f hpoints U).ge)
    (by rw [Scheme.Hom.resLE_comp_ι_assoc, hf]) (resLE_apply_eq_of_apply_eq f hpoints U)
    (F.restrict U.ι)
  exact ⟨restrictPullbackIso f hpoints U F ≪≫ β⟩

/-- **Stacks Project, Tag 0G05, clause (1).** Let `X` be a reduced scheme of finite type over a
field `k` and let `f : X ⟶ X` be an automorphism over `k` which induces the identity map on the
underlying topological space of `X`. Then every `𝒪_X`-module is isomorphic to its pullback along
`f`.

Nothing is carried and no hypothesis is put on `k`; coherence of the module is not needed. The
source's proof is "part (1) follows from part (2) and the fact that the connected components of
`X` of dimension `0` are spectra of fields": the scheme has finitely many connected components,
each clopen, on each of them clause (2) applies unless it is a one-point scheme, where a module
is isomorphic to its twist through a basis, and the isomorphisms glue because the components are
pairwise disjoint. -/
@[stacks 0G05 "clause (1) in full: every module on a reduced scheme of finite type over `k` is \
isomorphic to its pullback along an automorphism over `k` fixing every point of the underlying \
space. No hypothesis on the base field, nothing carried, and the module is arbitrary rather than \
coherent. The connected components are clopen and finite in number; on each of them clause (2) \
applies, or the component is the spectrum of a finite extension of `k` and the twist of a module \
is isomorphic to it through a basis; the isomorphisms glue over the pairwise disjoint cover"]
theorem exists_iso_pullback_of_isIso_of_eq_on_points {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] [QuasiCompact p] [IsReduced X] (f : X ⟶ X) [IsIso f]
    (hf : f ≫ p = p) (hpoints : ∀ x : X, f x = x) (F : X.Modules) :
    Nonempty ((Scheme.Modules.pullback f).obj F ≅ F) := by
  classical
  let _ : TopologicalSpace.NoetherianSpace X := noetherianSpace_of_quasiCompact p
  let _ : Finite (_root_.ConnectedComponents X) :=
    TopologicalSpace.NoetherianSpace.finite_connectedComponents X
  have hcover := isOpenCover_connectedComponentOpen X
  let α : ∀ c : _root_.ConnectedComponents X,
      ((Scheme.Modules.pullback f).obj F).restrict (connectedComponentOpen c).ι ≅
        F.restrict (connectedComponentOpen c).ι := fun c ↦
    (exists_iso_restrict_connectedComponentOpen p f hf hpoints F c).some
  have hg : ⨆ c : _root_.ConnectedComponents X,
      (connectedComponentOpen (X := X) c).ι ''ᵁ
        (⊤ : (connectedComponentOpen c).toScheme.Opens) = ⊤ := by
    simp only [Scheme.Opens.ι_image_top]
    exact hcover
  have hψ : ∀ (c c' : _root_.ConnectedComponents X)
      (W₁ : (connectedComponentOpen (X := X) c).toScheme.Opens)
      (W₂ : (connectedComponentOpen (X := X) c').toScheme.Opens) (V : X.Opens)
      (h₁ : (connectedComponentOpen (X := X) c).ι ''ᵁ W₁ = V)
      (h₂ : (connectedComponentOpen (X := X) c').ι ''ᵁ W₂ = V),
      Stacks.AlgebraicGeometry.ModuleHomGlue.localApp _ (α c).hom h₁ =
        Stacks.AlgebraicGeometry.ModuleHomGlue.localApp _ (α c').hom h₂ := by
    intro c c' W₁ W₂ V h₁ h₂
    by_cases hcc : c = c'
    · subst hcc
      exact Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_congr _ (α c).hom h₁ h₂
    · have hV : V = ⊥ :=
        le_bot_of_le_connectedComponentOpen hcc (le_of_ι_image_eq h₁) (le_of_ι_image_eq h₂)
      let _ : Subsingleton Γ(F, V) := Stacks.Tag0B5PClopenLift.subsingleton_sections_bot F hV
      ext s
      exact Subsingleton.elim _ _
  obtain ⟨φ, hφ, -⟩ :=
    Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover
      (fun c : _root_.ConnectedComponents X ↦ (connectedComponentOpen (X := X) c).ι) hg
      (fun c ↦ (α c).hom) hψ
  have hiso : ∀ c : _root_.ConnectedComponents X,
      IsIso ((Scheme.Modules.restrictFunctor (connectedComponentOpen (X := X) c).ι).map φ) := by
    intro c
    rw [hφ c]
    infer_instance
  let _ : IsIso φ := Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict φ
    connectedComponentOpen hcover hiso
  exact ⟨asIso φ⟩

end AlgebraicGeometry

end
