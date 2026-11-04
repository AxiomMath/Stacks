module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceCover
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.AlgebraicBaseChangeDomination
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FundamentalGroupOfLimit
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.ImageStabilizer
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedSeparablyClosed
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The fundamental exact sequence of a scheme over a field

Let `k` be a field with algebraic closure `k̄` and let `X` be a quasi-compact quasi-separated
scheme over `k` whose base change `X_k̄` is connected. This file proves Stacks Tag 0BTX: the
sequence

```
1 → π₁(X_k̄) → π₁(X) → π₁(Spec k) → 1
```

is a short exact sequence of profinite topological groups.

## The argument for exactness in the middle

That the composite is trivial is
`AlgebraicGeometry.etaleFundamentalGroupMap_comp_eq_one_isAlgClosed`. For the converse, let
`g ∈ π₁(X)` map to `1` in `π₁(Spec k)`, and write `K_s` for the separable closure of `k` in `k̄`.

* For every finite subset `s ⊆ K_s` the field `k[s]` is finite separable over `k`, so
  `X_{k[s]} = Spec k[s] ×_k X ⟶ X` is a finite étale cover which is the base change of the cover
  `Spec k[s]` of `Spec k`. The image of `π₁(X_{k[s]})` in `π₁(X)` is the stabilizer of the
  canonical point of the geometric fibre of `X_{k[s]}`
  (`AlgebraicGeometry.range_etaleFundamentalGroupMap_eq_stabilizer`), and since that fibre is the
  fibre of `Spec k[s]`, on which `g` acts through its trivial image in `π₁(Spec k)`, the element
  `g` lies in it.
* The preimages of `g` are unique, because `π₁(X_{k[s]}) → π₁(X)` is injective for a finite étale
  cover, hence compatible, and Stacks Tag 0BTV
  (`AlgebraicGeometry.etaleFundamentalGroup_homeomorph_compatibleFamilies`) glues them to an
  element of `π₁(X_{K_s})` mapping to `g`.
* `X_k̄ ⟶ X_{K_s}` is a universal homeomorphism, so it keeps connected finite étale covers
  connected and `π₁(X_k̄) → π₁(X_{K_s})` is surjective.

This gives the image of `π₁(X_k̄)` *equal* to the kernel, so in particular the image is normal; no
separate normality argument and no closure of a normal closure is involved.

## Main results

* `AlgebraicGeometry.mem_range_etaleFundamentalGroupMap_pullbackSnd_of_map_eq_one` — an element of
  `π₁(X)` acting trivially on `π₁(B)` comes from the base change `W ×_B X` of any finite étale
  cover `W` of `B`.
* `AlgebraicGeometry.surjective_etaleFundamentalGroupMap_of_universalHomeomorphism`.
* `AlgebraicGeometry.ker_le_range_etaleFundamentalGroupMap_isAlgClosed`.
* `AlgebraicGeometry.range_etaleFundamentalGroupMap_eq_ker_isAlgClosed` — exactness in the middle.
* `AlgebraicGeometry.topologicalShortExact_etaleFundamentalGroupMap_isAlgClosure` — the short
  exact sequence `1 → π₁(X_k̄) → π₁(X) → π₁(Spec k) → 1`.
* `AlgebraicGeometry.range_etaleFundamentalGroupMap_eq_ker_of_isPullback_isAlgClosed` and
  `AlgebraicGeometry.normal_range_etaleFundamentalGroupMap_of_isPullback_isAlgClosed` — the
  middle exactness, hence normality of the image, for a base change `X'` of `X` to *any*
  algebraically closed extension `K` of `k`, given as a pullback square.

## Arbitrary algebraically closed extensions

For `K` algebraically closed but not algebraic over `k`, let `k̄ ⊆ K` be the algebraic closure of
`k` in `K`. The base change `X_K ⟶ X_k̄` induces a surjection of fundamental groups: a connected
finite étale cover `V` of `X_k̄` is a connected scheme over the algebraically closed field `k̄`,
so `V ×_k̄ K = V ×_{X_k̄} X_K` is connected by Stacks Tag 0363. Hence the image of `π₁(X_K)` in
`π₁(X)` is that of `π₁(X_k̄)`, which is the kernel of `π₁(X) → π₁(Spec k)`. This needs neither
properness of `X` nor Stacks Tag 0A49.

## References

* [Stacks Project, Tag 0BTX](https://stacks.math.columbia.edu/tag/0BTX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.FundamentalGroup

universe u

namespace AlgebraicGeometry

/-! ### Elements acting trivially downstairs lift to base changes of covers -/

/-- **An element of `π₁(X)` killed by `π₁(X) → π₁(B)` comes from every base-changed cover.** Let
`f : X ⟶ B` be a morphism of connected schemes and `W` a finite étale cover of `B` whose base
change `W ×_B X` is connected. An element of `π₁(X)` mapping to `1` in `π₁(B)` lies in the image
of `π₁(W ×_B X)`: that image is the stabilizer of the canonical point of the geometric fibre of
`W ×_B X ⟶ X`, and this fibre projects bijectively and equivariantly onto the fibre of `W`, on
which the element acts trivially. -/
theorem mem_range_etaleFundamentalGroupMap_pullbackSnd_of_map_eq_one {B X : Scheme.{u}}
    [ConnectedSpace B] [ConnectedSpace X] (f : X ⟶ B) (W : FiniteEtaleOver B)
    [ConnectedSpace ↥(pullback W.hom f)] (t : GeometricPoint (pullback W.hom f))
    (g : EtaleFundamentalGroup X (t.map (pullback.snd W.hom f)))
    (hg : etaleFundamentalGroupMap f (t.map (pullback.snd W.hom f)) g = 1) :
    g ∈ (etaleFundamentalGroupMap (pullback.snd W.hom f) t).toMonoidHom.range := by
  have hf : finiteEtale (pullback.snd W.hom f) := ((finiteEtaleBaseChange f).obj W).prop
  rw [range_etaleFundamentalGroupMap_eq_stabilizer hf t, MulAction.mem_stabilizer_iff]
  apply (finiteEtaleFiberProjectionEquiv f (t.map (pullback.snd W.hom f)) W).injective
  have h := etaleFundamentalGroupMap_finiteEtaleFiberProjection f
    (t.map (pullback.snd W.hom f)) W g (finiteEtaleOverSourcePoint hf t)
  rwa [hg] at h

/-- A form of `AlgebraicGeometry.mem_range_etaleFundamentalGroupMap_pullbackSnd_of_map_eq_one`
at a geometric point of `X` only equal to the image of `t`, with the preimage related to the
given element by a heterogeneous equality. -/
theorem exists_heq_etaleFundamentalGroupMap_pullbackSnd_of_map_eq_one {B X : Scheme.{u}}
    [ConnectedSpace B] [ConnectedSpace X] (f : X ⟶ B) (W : FiniteEtaleOver B)
    [ConnectedSpace ↥(pullback W.hom f)] (t : GeometricPoint (pullback W.hom f))
    {z : GeometricPoint X} (hz : t.map (pullback.snd W.hom f) = z)
    (g : EtaleFundamentalGroup X z) (hg : etaleFundamentalGroupMap f z g = 1) :
    ∃ σ : EtaleFundamentalGroup (pullback W.hom f) t,
      HEq (etaleFundamentalGroupMap (pullback.snd W.hom f) t σ) g := by
  subst hz
  obtain ⟨σ, hσ⟩ := mem_range_etaleFundamentalGroupMap_pullbackSnd_of_map_eq_one f W t g hg
  exact ⟨σ, heq_of_eq hσ⟩

/-- Elements of fundamental groups at two equal geometric points with heterogeneously equal
images under a homomorphism that is injective at every geometric point are heterogeneously
equal. -/
theorem heq_of_heq_etaleFundamentalGroupMap {A B : Scheme.{u}} [ConnectedSpace A]
    [ConnectedSpace B] (p : A ⟶ B)
    (hinj : ∀ a : GeometricPoint A, Function.Injective (etaleFundamentalGroupMap p a))
    {a a' : GeometricPoint A} (ha : a = a') {σ : EtaleFundamentalGroup A a}
    {σ' : EtaleFundamentalGroup A a'}
    (h : HEq (etaleFundamentalGroupMap p a σ) (etaleFundamentalGroupMap p a' σ')) :
    HEq σ σ' := by
  subst ha
  exact heq_of_eq (hinj a (eq_of_heq h))

/-- Mapping a geometric point along two morphisms is mapping it along any morphism equal to their
composite. -/
theorem GeometricPoint.map_map_of_comp_eq {A B C : Scheme.{u}} (x : GeometricPoint A) (a : A ⟶ B)
    (b : B ⟶ C) {c : A ⟶ C} (h : a ≫ b = c) : (x.map a).map b = x.map c := by
  subst h
  cases x
  simp [GeometricPoint.map]

/-- **Gluing preimages along a limit.** Let `c` be a limit of a cofiltered diagram `D` of qcqs
schemes with affine transition maps and connected cofinal tail over `i₀`, mapping compatibly to `X`
by morphisms injective on fundamental groups. An element of `π₁(X)` with a preimage in the
fundamental group of every stage of the tail has a preimage in `π₁(c.pt)`. -/
private theorem exists_heq_etaleFundamentalGroupMap_of_isLimit {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)] [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)] (i₀ : I)
    [∀ j : Over i₀, ConnectedSpace (D.obj j.left)] {X : Scheme.{u}} [ConnectedSpace X]
    [ConnectedSpace c.pt] (π : ∀ j : Over i₀, D.obj j.left ⟶ X) (p : c.pt ⟶ X)
    (hcπ : ∀ j, c.π.app j.left ≫ π j = p)
    (hDπ : ∀ {i j : Over i₀} (e : i ⟶ j), D.map e.left ≫ π j = π i)
    (hinj : ∀ j a, Function.Injective (etaleFundamentalGroupMap (π j) a))
    (y : GeometricPoint c.pt) {z : GeometricPoint X} (hz : y.map p = z)
    (g : EtaleFundamentalGroup X z)
    (hg : ∀ j : Over i₀, ∃ σ : EtaleFundamentalGroup (D.obj j.left) (y.map (c.π.app j.left)),
      HEq (etaleFundamentalGroupMap (π j) (y.map (c.π.app j.left)) σ) g) :
    ∃ τ : EtaleFundamentalGroup c.pt y, HEq (etaleFundamentalGroupMap p y τ) g := by
  subst hz
  choose σ hσ using hg
  have hcompat : CompatibleFundamentalGroupFamily D c i₀ y σ := fun {i j} e ↦
    heq_of_heq_etaleFundamentalGroupMap (π j) (hinj j) (geometricPoint_map_cone D c y e.left)
      ((etaleFundamentalGroupMap_triangle (D.map e.left) (π j) (π i) (hDπ e) _ (σ i)).trans
        ((hσ i).trans (hσ j).symm))
  obtain ⟨hX', hG, hTG, e, he⟩ := etaleFundamentalGroup_homeomorph_compatibleFamilies D c hc i₀ y
  have : ConnectedSpace (((Functor.const I).obj c.pt).obj i₀) :=
    inferInstanceAs (ConnectedSpace c.pt)
  have : ConnectedSpace (D.obj i₀) :=
    inferInstanceAs (ConnectedSpace (D.obj (Over.mk (𝟙 i₀)).left))
  obtain ⟨τ, hτe⟩ := e.surjective ⟨σ, hcompat⟩
  have hτ : etaleFundamentalGroupMap (c.π.app i₀) y τ = σ (Over.mk (𝟙 i₀)) := by
    have h₀ := he τ (Over.mk (𝟙 i₀))
    rw [hτe] at h₀
    exact h₀.symm
  refine ⟨τ, (etaleFundamentalGroupMap_triangle (c.π.app i₀) (π (Over.mk (𝟙 i₀))) p
    (hcπ _) y τ).symm.trans ?_⟩
  rw [hτ]
  exact hσ _

/-! ### Universal homeomorphisms -/

/-- **Condition (3) of Stacks 0BN6 gives surjectivity on étale fundamental groups.** If base change
along `h : X ⟶ Y` keeps every connected finite étale cover of `Y` connected, then
`π₁(X, x) → π₁(Y, h ∘ x)` is surjective. -/
@[sga "7 XVIII 6.1.5" "partial"]
theorem surjective_etaleFundamentalGroupMap_of_isConnected_finiteEtaleBaseChange
    {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y] (h : X ⟶ Y) (x : GeometricPoint X)
    (hconn : ∀ V : FiniteEtaleOver Y, PreGaloisCategory.IsConnected V →
      PreGaloisCategory.IsConnected ((finiteEtaleBaseChange h).obj V)) :
    Function.Surjective (etaleFundamentalGroupMap h x) := by
  let H := finiteEtaleBaseChange h
  let F := finiteEtaleFiberFintypeFunctor Y (x.map h)
  let F' := finiteEtaleFiberFintypeFunctor X x
  let t := finiteEtaleFiberFintypeFunctorBaseChangeIso h x
  let d := galoisFunctorDataOfFiberIso F F' H t
  let _gF : IsGaloisCategory (setValuedFiberFunctor F) :=
    isGaloisCategory_setValuedFiberFunctor_finiteEtaleFiberFintypeFunctor Y (x.map h)
  let _gF' : IsGaloisCategory (setValuedFiberFunctor F') :=
    isGaloisCategory_setValuedFiberFunctor_finiteEtaleFiberFintypeFunctor X x
  let star := finiteEtaleOverTerminal Y
  let star' := finiteEtaleOverTerminal X
  have hs : IsTerminal star := MorphismProperty.Over.mkIdTerminal _ _
  have hs' : IsTerminal star' := MorphismProperty.Over.mkIdTerminal _ _
  have hH := exactFunctor_finiteEtaleBaseChange h x
  have : PreservesFiniteLimits H := hH.1
  have hHs : IsTerminal (H.obj star) := hs.isTerminalObj H star
  have hdsurj : Function.Surjective d.hom :=
    ((surjective_inducedHom_tfae F F' H hH t d star star' hs hs' hHs).out 3 1).mp hconn
  intro ρ
  obtain ⟨σ, hσ⟩ := hdsurj ((autMulEquivEtaleFundamentalGroup Y (x.map h)).symm ρ)
  refine ⟨autMulEquivEtaleFundamentalGroup X x σ, ?_⟩
  rw [← autMulEquivEtaleFundamentalGroup_galoisFunctorData_hom h x d σ, hσ]
  exact (autMulEquivEtaleFundamentalGroup Y (x.map h)).apply_symm_apply ρ

/-- **A universal homeomorphism induces a surjection of étale fundamental groups.** A connected
finite étale cover `V` of the target stays connected after base change, since the projection
`V ×_Y X ⟶ V` is a homeomorphism; this is the third condition of Stacks 0BN6. -/
@[sga "1 IX 5.6" "special case"]
theorem surjective_etaleFundamentalGroupMap_of_universalHomeomorphism {X Y : Scheme.{u}}
    [ConnectedSpace X] [ConnectedSpace Y] (h : X ⟶ Y) [UniversalHomeomorphism h]
    (x : GeometricPoint X) :
    Function.Surjective (etaleFundamentalGroupMap h x) := by
  refine surjective_etaleFundamentalGroupMap_of_isConnected_finiteEtaleBaseChange h x
    fun V hV ↦ ?_
  have hconn : ConnectedSpace ↥(pullback V.hom h) :=
    ((Stacks.Etale.isHomeomorph_pullbackFst h V.hom).homeomorph _).connectedSpace_iff.mpr
      (connectedSpace_left_of_isConnected V hV)
  exact @isConnected_of_connectedSpace_left _ ((finiteEtaleBaseChange h).obj V) hconn

/-! ### Exactness in the middle -/

/-- The spectrum maps of a scalar tower of fields `k → L → M` compose. -/
private theorem specMap_algebraMap_comp_specMap_algebraMap (k L M : Type u) [Field k] [Field L]
    [Field M] [Algebra k L] [Algebra L M] [Algebra k M] [IsScalarTower k L M] :
    Spec.map (CommRingCat.ofHom (algebraMap L M)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) =
      Spec.map (CommRingCat.ofHom (algebraMap k M)) := by
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

/-- The stages of `AlgebraicGeometry.AdjoinFinset.bcDiagram` over a quasi-compact quasi-separated
scheme are quasi-compact and quasi-separated: they are affine over it. -/
private theorem AdjoinFinset.compactSpace_and_quasiSeparatedSpace_bcDiagram_obj (k k' : Type u)
    [CommRing k] [CommRing k'] [Algebra k k'] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [CompactSpace X] [QuasiSeparatedSpace X] (i : (Finset k')ᵒᵖ) :
    CompactSpace ((bcDiagram k k' f).obj i) ∧ QuasiSeparatedSpace ((bcDiagram k k' f).obj i) := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap k (Algebra.adjoin k (i.unop : Set k'))))
  have : IsAffineHom (pullback.snd s f) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback s f)
      (isAffineHom_of_isAffine _)
  show CompactSpace ↥(pullback s f) ∧ QuasiSeparatedSpace ↥(pullback s f)
  exact ⟨QuasiCompact.compactSpace_of_compactSpace (pullback.snd s f),
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd s f)⟩

section Middle

variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]

/-- The finite étale cover `Spec k[s]` of `Spec k` attached to a finite subset `s` of a separable
algebraic extension. -/
def adjoinFinsetFiniteEtaleOver (K : Type u) [Field K] [Algebra k K] [Algebra.IsSeparable k K]
    (s : Finset K) : FiniteEtaleOver (Spec (.of k)) :=
  MorphismProperty.Over.mk ⊤
    (Spec.map (CommRingCat.ofHom (algebraMap k (Algebra.adjoin k (s : Set K)))))
    (finiteEtale_specMap_algebraMap_adjoin k K s)

/-- The base change `X_{k[s]}` is connected when `X_Ω` is, for `Ω` algebraically closed. -/
private theorem connectedSpace_pullback_adjoinFinsetFiniteEtaleOver [IsAlgClosed Ω] (K : Type u)
    [Field K] [Algebra k K] [Algebra.IsSeparable k K] (s : Finset K) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k))
    [ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))] :
    ConnectedSpace ↥(pullback (adjoinFinsetFiniteEtaleOver k K s).hom f) := by
  have h₁ := (finiteEtale_specMap_algebraMap_adjoin k K s).1
  have h₂ := (finiteEtale_specMap_algebraMap_adjoin k K s).2
  let : Field (Algebra.adjoin k (s : Set K)) := (Subalgebra.isField_of_algebraic _).toField
  exact connectedSpace_pullback_of_connectedSpace_pullback_specMap_algebraMap k Ω f
    (Spec.map (CommRingCat.ofHom (algebraMap k (Algebra.adjoin k (s : Set K)))))

/-- **The kernel of `π₁(X) → π₁(Spec k)` lies in the image of `π₁(X_{K_s})`**, for `K_s` the
separable closure of `k` in an algebraically closed extension `Ω` with `X_Ω` connected: the
preimages of an element of the kernel in the `π₁(X_{k[s]})` glue by Stacks 0BTV. -/
private theorem exists_heq_etaleFundamentalGroupMap_separableClosure_of_map_eq_one [IsAlgClosed Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [CompactSpace X] [QuasiSeparatedSpace X]
    [ConnectedSpace X]
    [ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))]
    [ConnectedSpace ↥(pullback (Spec.map (CommRingCat.ofHom
      (algebraMap k (separableClosure k Ω)))) f)]
    (y : GeometricPoint (pullback (Spec.map (CommRingCat.ofHom
      (algebraMap k (separableClosure k Ω)))) f))
    {z : GeometricPoint X} (hz : y.map (pullback.snd _ f) = z) (g : EtaleFundamentalGroup X z)
    (hg : etaleFundamentalGroupMap f z g = 1) :
    ∃ τ : EtaleFundamentalGroup _ y, HEq (etaleFundamentalGroupMap (pullback.snd _ f) y τ) g := by
  let Ks := separableClosure k Ω
  let D := AdjoinFinset.bcDiagram k Ks f
  let c := AdjoinFinset.bcCone k Ks f
  have hD := AdjoinFinset.compactSpace_and_quasiSeparatedSpace_bcDiagram_obj k Ks f
  have : ∀ i, CompactSpace (D.obj i) := fun i ↦ (hD i).1
  have : ∀ i, QuasiSeparatedSpace (D.obj i) := fun i ↦ (hD i).2
  have : ∀ {i j : (Finset Ks)ᵒᵖ} (e : i ⟶ j), IsAffineHom (D.map e) :=
    fun e ↦ AdjoinFinset.bcDiagram_isAffineHom k Ks f e
  let W : (Finset Ks)ᵒᵖ → FiniteEtaleOver (Spec (.of k)) :=
    fun i ↦ adjoinFinsetFiniteEtaleOver k Ks i.unop
  have hconnI : ∀ i : (Finset Ks)ᵒᵖ, ConnectedSpace ↥(pullback (W i).hom f) := fun i ↦
    connectedSpace_pullback_adjoinFinsetFiniteEtaleOver k Ω Ks i.unop f
  let i₀ : (Finset Ks)ᵒᵖ := Opposite.op ∅
  have hconn : ∀ j : Over i₀, ConnectedSpace (D.obj j.left) := fun j ↦ hconnI j.left
  have : ConnectedSpace c.pt := inferInstanceAs (ConnectedSpace ↥(pullback
    (Spec.map (CommRingCat.ofHom (algebraMap k Ks))) f))
  let π : ∀ i : (Finset Ks)ᵒᵖ, pullback (W i).hom f ⟶ X := fun i ↦ pullback.snd (W i).hom f
  have hπ : ∀ i, finiteEtale (π i) := fun i ↦ ((finiteEtaleBaseChange f).obj (W i)).prop
  have hcπ : ∀ i, c.π.app i ≫ π i = pullback.snd _ f := fun i ↦
    AdjoinFinset.bcProj_snd k Ks f i
  have hpt : ∀ i : (Finset Ks)ᵒᵖ, (y.map (c.π.app i)).map (π i) = z := fun i ↦
    (GeometricPoint.map_map_of_comp_eq y _ _ (hcπ i)).trans hz
  exact exists_heq_etaleFundamentalGroupMap_of_isLimit D c (AdjoinFinset.isLimitBcCone k Ks f) i₀
    (fun j ↦ π j.left) (pullback.snd _ f) (fun j ↦ hcπ j.left)
    (fun e ↦ Over.w ((Over.pullback f).map ((AdjoinFinset.specOverDiagram k Ks).map e.left)))
    (fun j a ↦ injective_etaleFundamentalGroupMap_of_dominatesFiniteEtale _ a
      (@dominatesFiniteEtale_of_finiteEtale _ _ (π j.left) (hπ j.left).1 (hπ j.left).2))
    y hz g fun j ↦ exists_heq_etaleFundamentalGroupMap_pullbackSnd_of_map_eq_one f (W j.left)
      (y.map (c.π.app j.left)) (hpt j.left) g hg

/-- **The kernel of `π₁(X) → π₁(Spec k)` lies in the image of `π₁(X_Ω)`**, for an algebraically
closed algebraic extension `Ω/k` and a quasi-compact quasi-separated scheme `X` over `k` with
`X_Ω` connected. See the module docstring for the argument. -/
theorem ker_le_range_etaleFundamentalGroupMap_isAlgClosed [IsAlgClosed Ω]
    [Algebra.IsAlgebraic k Ω] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [CompactSpace X]
    [QuasiSeparatedSpace X]
    [ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))]
    (x : GeometricPoint (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))) :
    letI : ConnectedSpace ↥X := connectedSpace_of_connectedSpace_pullback_specMap_algebraMap k Ω f
    (etaleFundamentalGroupMap f
        (x.map (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))))).toMonoidHom.ker
      ≤ (etaleFundamentalGroupMap (pullback.fst f
          (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) x).toMonoidHom.range := by
  let : ConnectedSpace ↥X := connectedSpace_of_connectedSpace_pullback_specMap_algebraMap k Ω f
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  let Ks := separableClosure k Ω
  let sKs := Spec.map (CommRingCat.ofHom (algebraMap k Ks))
  let sK := Spec.map (CommRingCat.ofHom (algebraMap k Ω))
  let ι := Spec.map (CommRingCat.ofHom (algebraMap Ks Ω))
  have hι : ι ≫ sKs = sK := specMap_algebraMap_comp_specMap_algebraMap k Ks Ω
  -- The universal homeomorphism `X_Ω ⟶ X_{K_s}`.
  let h : pullback f sK ⟶ pullback sKs f :=
    pullback.lift (pullback.snd f sK ≫ ι) (pullback.fst f sK) (by
      rw [Category.assoc, hι, pullback.condition])
  have hcomp : h ≫ pullback.snd sKs f = pullback.fst f sK := pullback.lift_snd _ _ _
  have : UniversalHomeomorphism h := by
    have outer : IsPullback (h ≫ pullback.snd sKs f) (pullback.snd f sK) f (ι ≫ sKs) := by
      rw [hcomp, hι]
      exact IsPullback.of_hasPullback f sK
    have hpb : IsPullback h (pullback.snd f sK) (pullback.fst sKs f) ι :=
      IsPullback.of_right outer (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback sKs f).flip
    exact ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip
      (Stacks.EtaleCohomology.specMap_universalHomeomorphism_of_isPurelyInseparable
        Ks Ω).universally_isHomeomorph⟩
  have : Surjective h := Stacks.Etale.surjective_of_universalHomeomorphism h
  have : ConnectedSpace ↥(pullback sKs f) := h.surjective.connectedSpace h.continuous
  obtain ⟨τ, hτg⟩ := exists_heq_etaleFundamentalGroupMap_separableClosure_of_map_eq_one k Ω f
    (x.map h) (GeometricPoint.map_map_of_comp_eq x h _ hcomp) g hg
  -- Lift along the universal homeomorphism.
  obtain ⟨ρ, hρ⟩ := surjective_etaleFundamentalGroupMap_of_universalHomeomorphism h x τ
  refine ⟨ρ, eq_of_heq ?_⟩
  refine (etaleFundamentalGroupMap_triangle h (pullback.snd sKs f) (pullback.fst f sK) hcomp x
    ρ).symm.trans ?_
  rw [hρ]
  exact hτg

/-- **Exactness in the middle of the sequence of Stacks Tag 0BTX.** For an algebraically closed
algebraic extension `Ω/k` and a quasi-compact quasi-separated scheme `X` over `k` with `X_Ω`
connected, the image of `π₁(X_Ω) → π₁(X)` is the kernel of `π₁(X) → π₁(Spec k)`. -/
theorem range_etaleFundamentalGroupMap_eq_ker_isAlgClosed [IsAlgClosed Ω]
    [Algebra.IsAlgebraic k Ω] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [CompactSpace X]
    [QuasiSeparatedSpace X]
    [ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))]
    (x : GeometricPoint (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))) :
    letI : ConnectedSpace ↥X := connectedSpace_of_connectedSpace_pullback_specMap_algebraMap k Ω f
    (etaleFundamentalGroupMap
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) x).toMonoidHom.range =
      (etaleFundamentalGroupMap f (x.map (pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))))).toMonoidHom.ker := by
  let : ConnectedSpace ↥X := connectedSpace_of_connectedSpace_pullback_specMap_algebraMap k Ω f
  refine le_antisymm ?_ (ker_le_range_etaleFundamentalGroupMap_isAlgClosed k Ω f x)
  rintro _ ⟨σ, rfl⟩
  rw [MonoidHom.mem_ker]
  exact DFunLike.congr_fun (etaleFundamentalGroupMap_comp_eq_one_isAlgClosed k Ω f x) σ

end Middle

/-! ### Stacks Tag 0BTX -/

/-- **Stacks Project, Tag 0BTX.** Let `k` be a field with algebraic closure `k̄` and let `X` be a
quasi-compact and quasi-separated scheme over `k` whose base change `X_k̄` is connected. Then `X`
is connected (`AlgebraicGeometry.connectedSpace_of_connectedSpace_pullback_specMap_algebraMap`)
and, for a geometric point `x` of `X_k̄`,

```
1 → π₁(X_k̄, x) → π₁(X, x) → π₁(Spec k, x) → 1
```

is a short exact sequence of profinite topological groups: the first map is injective and a
closed embedding, its image is the kernel of the second, and the second is surjective and a
quotient map. Both maps are the continuous homomorphisms induced by the projection
`X_k̄ ⟶ X` and the structure morphism `X ⟶ Spec k`; the three groups carry their profinite
topologies (`AlgebraicGeometry.etaleFundamentalGroupCompactSpace` and its companions). -/
@[stacks 0BTX, sga "1 XIII 4.0" "vu = 1", sga "1 XIII 4.4" "special case"]
theorem topologicalShortExact_etaleFundamentalGroupMap_isAlgClosure (k kbar : Type u) [Field k]
    [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [CompactSpace X] [QuasiSeparatedSpace X]
    [ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (x : GeometricPoint (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))) :
    letI : ConnectedSpace ↥X :=
      connectedSpace_of_connectedSpace_pullback_specMap_algebraMap k kbar f
    Function.Injective (etaleFundamentalGroupMap
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) x) ∧
      Topology.IsClosedEmbedding (etaleFundamentalGroupMap
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) x) ∧
      (etaleFundamentalGroupMap
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) x).toMonoidHom.range =
        (etaleFundamentalGroupMap f
          (x.map (pullback.fst f
            (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))))).toMonoidHom.ker ∧
      Function.Surjective (etaleFundamentalGroupMap f
          (x.map (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))))) ∧
      Topology.IsQuotientMap (etaleFundamentalGroupMap f
          (x.map (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))))) := by
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : Algebra.IsAlgebraic k kbar := IsAlgClosure.isAlgebraic
  let : ConnectedSpace ↥X :=
    connectedSpace_of_connectedSpace_pullback_specMap_algebraMap k kbar f
  have := forall_finite_finiteEtaleFiberFunctor_obj x
  have := forall_finite_finiteEtaleFiberFunctor_obj
    (x.map (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))))
  have := forall_finite_finiteEtaleFiberFunctor_obj
    ((x.map (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))).map f)
  have hinj := injective_etaleFundamentalGroupMap_of_isAlgebraic k kbar f x
  have hsurj := surjective_etaleFundamentalGroupMap_isAlgClosed k kbar f
    (x.map (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))))
  exact ⟨hinj, (map_continuous _).isClosedEmbedding hinj,
    range_etaleFundamentalGroupMap_eq_ker_isAlgClosed k kbar f x, hsurj,
    (map_continuous _).isClosedMap.isQuotientMap (map_continuous _) hsurj⟩

/-! ### Base change to an arbitrary algebraically closed extension -/

section IsPullback

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- The spectrum map of a field extension is surjective: its target is a single point. -/
theorem surjective_specMap_algebraMap_field (k K : Type u) [Field k] [Field K] [Algebra k K] :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
  ⟨fun _ ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩

/-- A scheme over `k` is connected as soon as some base change of it to a field extension of `k`
is connected: the projection is a base change of the surjection `Spec K ⟶ Spec k`. -/
theorem connectedSpace_of_isPullback_specMap_algebraMap {X X' : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (q : X' ⟶ X) (fK : X' ⟶ Spec (.of K))
    (hbc : IsPullback q fK f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    [ConnectedSpace X'] : ConnectedSpace X := by
  have : Surjective q := MorphismProperty.of_isPullback (P := @Surjective) hbc.flip
    (surjective_specMap_algebraMap_field k K)
  exact q.surjective.connectedSpace q.continuous

/-- **Base change to an extension of an algebraically closed field is surjective on `π₁`.** For
`kb` algebraically closed and `X'` a base change of a connected `Y` over `kb` to an extension `K`,
`π₁(X') → π₁(Y)` is surjective: by Stacks 0363 a connected finite étale cover of `Y` stays
connected after base change to `K`. -/
private theorem surjective_etaleFundamentalGroupMap_of_isPullback_isAlgClosed (kb : Type u)
    [Field kb] [Algebra kb K] [IsAlgClosed kb] {Y X' : Scheme.{u}} [ConnectedSpace Y]
    [ConnectedSpace X']
    (p : Y ⟶ Spec (.of kb)) (m : X' ⟶ Y) (fK : X' ⟶ Spec (.of K))
    (hm : IsPullback m fK p (Spec.map (CommRingCat.ofHom (algebraMap kb K))))
    (x : GeometricPoint X') : Function.Surjective (etaleFundamentalGroupMap m x) := by
  refine surjective_etaleFundamentalGroupMap_of_isConnected_finiteEtaleBaseChange m x
    fun V hV ↦ ?_
  let ι := Spec.map (CommRingCat.ofHom (algebraMap kb K))
  have : IsSepClosed kb := IsSepClosed.of_isAlgClosed kb
  have : GeometricallyConnected (V.hom ≫ p) :=
    (geometricallyConnected_iff_connectedSpace kb (V.hom ≫ p)).mpr
      (connectedSpace_left_of_isConnected V hV)
  have hpb : IsPullback (pullback.fst V.hom m) (pullback.snd V.hom m ≫ fK) (V.hom ≫ p) ι :=
    (IsPullback.of_hasPullback V.hom m).paste_vert hm
  have : ConnectedSpace ↥(pullback (V.hom ≫ p) ι) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := pullback.snd (V.hom ≫ p) ι)
  exact @isConnected_of_connectedSpace_left _ ((finiteEtaleBaseChange m).obj V)
    ((Scheme.homeoOfIso hpb.isoPullback).connectedSpace_iff.mpr inferInstance)

/-- **Exactness in the middle passes along a surjection on `π₁`.** If `π₁(Y) → π₁(X) → π₁(B)` is
exact in the middle and `π₁(X') → π₁(Y)` is surjective, then so is `π₁(X') → π₁(X) → π₁(B)` for the
composite `q = m ≫ r : X' ⟶ X`. -/
private theorem range_etaleFundamentalGroupMap_eq_ker_of_comp_of_surjective {X' Y X B : Scheme.{u}}
    [ConnectedSpace X'] [ConnectedSpace Y] [ConnectedSpace X] [ConnectedSpace B] (m : X' ⟶ Y)
    (r : Y ⟶ X) (f : X ⟶ B) (q : X' ⟶ X) (hm : m ≫ r = q) (x : GeometricPoint X')
    (hsurj : Function.Surjective (etaleFundamentalGroupMap m x))
    (hmid : (etaleFundamentalGroupMap r (x.map m)).toMonoidHom.range =
      (etaleFundamentalGroupMap f ((x.map m).map r)).toMonoidHom.ker) :
    (etaleFundamentalGroupMap q x).toMonoidHom.range =
      (etaleFundamentalGroupMap f (x.map q)).toMonoidHom.ker := by
  have key : ∀ (z : GeometricPoint X) (hz : (x.map m).map r = z)
      (g : EtaleFundamentalGroup X z),
      etaleFundamentalGroupMap f z g = 1 ↔
        ∃ τ : EtaleFundamentalGroup X' x, HEq (etaleFundamentalGroupMap q x τ) g := by
    intro z hz g
    subst hz
    have htri : ∀ τ : EtaleFundamentalGroup X' x, HEq (etaleFundamentalGroupMap r (x.map m)
        (etaleFundamentalGroupMap m x τ)) (etaleFundamentalGroupMap q x τ) :=
      fun τ ↦ etaleFundamentalGroupMap_triangle m r q hm x τ
    constructor
    · intro hg
      obtain ⟨ρ, rfl⟩ : g ∈ (etaleFundamentalGroupMap r (x.map m)).toMonoidHom.range :=
        hmid ▸ MonoidHom.mem_ker.mpr hg
      obtain ⟨τ, rfl⟩ := hsurj ρ
      exact ⟨τ, (htri τ).symm⟩
    · rintro ⟨τ, hτ⟩
      have hτ' : etaleFundamentalGroupMap r (x.map m) (etaleFundamentalGroupMap m x τ) = g :=
        eq_of_heq ((htri τ).trans hτ)
      have hmem : g ∈ (etaleFundamentalGroupMap f ((x.map m).map r)).toMonoidHom.ker :=
        hmid ▸ ⟨_, hτ'⟩
      exact MonoidHom.mem_ker.mp hmem
  ext g
  rw [MonoidHom.mem_ker]
  have hk := key (x.map q) (GeometricPoint.map_map_of_comp_eq x m _ hm) g
  constructor
  · rintro ⟨τ, rfl⟩
    exact hk.mpr ⟨τ, HEq.rfl⟩
  · intro hg
    obtain ⟨τ, hτ⟩ := hk.mp hg
    exact ⟨τ, eq_of_heq hτ⟩

/-- **Exactness in the middle of the sequence of Stacks Tag 0BTX for any algebraically closed
extension.** Let `K` be an algebraically closed extension of `k` (not necessarily algebraic), `X`
a quasi-compact quasi-separated scheme over `k` and `X'` a base change of `X` to `K`, given as a
pullback square, with `X'` connected. Then the image of `π₁(X') → π₁(X)` is the kernel of
`π₁(X) → π₁(Spec k)`. -/
theorem range_etaleFundamentalGroupMap_eq_ker_of_isPullback_isAlgClosed [IsAlgClosed K]
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of k)) [CompactSpace X] [QuasiSeparatedSpace X]
    (q : X' ⟶ X) (fK : X' ⟶ Spec (.of K))
    (hbc : IsPullback q fK f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    [ConnectedSpace X'] (x : GeometricPoint X') :
    letI : ConnectedSpace X := connectedSpace_of_isPullback_specMap_algebraMap k K f q fK hbc
    (etaleFundamentalGroupMap q x).toMonoidHom.range =
      (etaleFundamentalGroupMap f (x.map q)).toMonoidHom.ker := by
  let : ConnectedSpace X := connectedSpace_of_isPullback_specMap_algebraMap k K f q fK hbc
  let kb := algebraicClosure k K
  have : IsAlgClosed kb := IsAlgClosure.isAlgClosed k
  have : Algebra.IsAlgebraic k kb := IsAlgClosure.isAlgebraic
  let sb := Spec.map (CommRingCat.ofHom (algebraMap k kb))
  let sK := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let ι := Spec.map (CommRingCat.ofHom (algebraMap kb K))
  have hι : ι ≫ sb = sK := specMap_algebraMap_comp_specMap_algebraMap k kb K
  -- The comparison morphism `X' ⟶ X_k̄`, a base change of `Spec K ⟶ Spec k̄`.
  let m : X' ⟶ pullback f sb := pullback.lift q (fK ≫ ι) (by rw [Category.assoc, hι, hbc.w])
  have hm : m ≫ pullback.fst f sb = q := pullback.lift_fst _ _ _
  have hleft : IsPullback m fK (pullback.snd f sb) ι := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f sb)
    rw [hm, hι]
    exact hbc
  have : ConnectedSpace ↥(pullback f sb) :=
    connectedSpace_of_isPullback_specMap_algebraMap kb K (pullback.snd f sb) m fK hleft
  have hsurj := surjective_etaleFundamentalGroupMap_of_isPullback_isAlgClosed K kb
    (pullback.snd f sb) m fK hleft x
  exact range_etaleFundamentalGroupMap_eq_ker_of_comp_of_surjective m (pullback.fst f sb) f q hm
    x hsurj (range_etaleFundamentalGroupMap_eq_ker_isAlgClosed k kb f (x.map m))

/-- **The image of the geometric fundamental group is normal**, for a base change `X'` of a
quasi-compact quasi-separated scheme `X` over `k` to any algebraically closed extension `K` of
`k`, with `X'` connected: it is the kernel of `π₁(X) → π₁(Spec k)`. -/
theorem normal_range_etaleFundamentalGroupMap_of_isPullback_isAlgClosed [IsAlgClosed K]
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of k)) [CompactSpace X] [QuasiSeparatedSpace X]
    (q : X' ⟶ X) (fK : X' ⟶ Spec (.of K))
    (hbc : IsPullback q fK f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    [ConnectedSpace X'] (x : GeometricPoint X') :
    letI : ConnectedSpace X := connectedSpace_of_isPullback_specMap_algebraMap k K f q fK hbc
    (etaleFundamentalGroupMap q x).toMonoidHom.range.Normal := by
  let : ConnectedSpace X := connectedSpace_of_isPullback_specMap_algebraMap k K f q fK hbc
  rw [range_etaleFundamentalGroupMap_eq_ker_of_isPullback_isAlgClosed k K f q fK hbc x]
  exact MonoidHom.normal_ker _

end IsPullback

end AlgebraicGeometry

end
