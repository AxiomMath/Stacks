module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.HomotopySequenceComponents
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.HomotopySequenceGaloisLifting
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.HomotopySequenceSteinCover
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ProperFlatHomotopySequence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Exactness of the homotopy sequence of a proper flat family

Let `f : X ⟶ S` be a flat, proper morphism of finite presentation with geometrically connected
and geometrically reduced fibres, let `S` be connected, let `s` be a geometric point of `S` and
let `z` be a geometric point of the geometric fibre `X_s = X ×_S s`. The sequence

```
π₁(X_s, z) ⟶ π₁(X, z ∘ p) ⟶ π₁(S, z ∘ p ∘ f) ⟶ 1
```

is exact: the second map is surjective, the composite is trivial, and the kernel of the second
map is the smallest closed normal subgroup containing the image of the first.

## The descent step

Exactness follows from the criterion of [Stacks, Tag 0BS9], which asks for two things: that base
change of finite étale covers along `f` be fully faithful, and that a finite étale cover of `X`
come from `S` exactly when its base change to `X_s` is a finite coproduct of copies of `X_s`.
The first is `AlgebraicGeometry.fullyFaithful_finiteEtaleBaseChange_of_geometricallyConnected`
and the "only if" half of the second is
`AlgebraicGeometry.isFiniteCoproductOfTerminal_finiteEtaleBaseChange_geometricFibre`.

The "if" half is the Stein factorization argument. One reduces to a connected cover `V ⟶ X`, for
which the splitting over `X_s` provides a section `i : X_s ⟶ V ×_X X_s` of the projection. The
Stein factorization `V ⟶ T ⟶ S` of `V ⟶ S` has `T ⟶ S` finite étale, so `T ×_S X` is a finite
étale cover of `X`, and the comparison morphism `V ⟶ T ×_S X` is finite étale as well. The
section `i` makes its geometric fibre over a suitable geometric point a singleton: the first
factor `V ⟶ T` has geometrically connected fibres and is universally closed, hence induces a
bijection on connected components after base change, and the image of the section is clopen, so
it swallows whole fibres. A finite étale morphism onto a connected scheme with a one-point
geometric fibre is an isomorphism, so `V ≅ T ×_S X` comes from `S`.

## Main results

* `AlgebraicGeometry.isIso_steinComparison_of_section`: the comparison morphism to the base
  change of the Stein image is an isomorphism in the presence of a splitting over the geometric
  fibre.
* `AlgebraicGeometry.essImage_finiteEtaleBaseChange_iff_isFiniteCoproductOfTerminal`: the second
  condition of [Stacks, Tag 0BS9] for the pair of base-change functors.
* `AlgebraicGeometry.isExactSequence_etaleFundamentalGroupMap_of_properFlat`: the exact sequence
  itself.

## References

* [Stacks Project, Tag 0C0J](https://stacks.math.columbia.edu/tag/0C0J)
* [Stacks Project, Tag 0BUN](https://stacks.math.columbia.edu/tag/0BUN)
* [Stacks Project, Tag 0BS9](https://stacks.math.columbia.edu/tag/0BS9)
* [Stacks Project, Tag 03H2](https://stacks.math.columbia.edu/tag/03H2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.FundamentalGroup

universe u

namespace AlgebraicGeometry

/-! ### Recognising isomorphisms of finite étale covers on a geometric fibre -/

/-- A finite étale cover admitting an isomorphism to the terminal one has invertible structure
morphism. -/
private theorem isIso_hom_of_isIso_to_finiteEtaleOverTerminal {B : Scheme.{u}}
    {V : FiniteEtaleOver B} (g : V ⟶ finiteEtaleOverTerminal B) [IsIso g] : IsIso V.hom := by
  have : IsIso (finiteEtaleOverTerminal B).hom := inferInstanceAs (IsIso (𝟙 B))
  have : IsIso g.left :=
    (Over.forget B).map_isIso ((MorphismProperty.Over.forget
      (finiteEtale : MorphismProperty Scheme.{u}) ⊤ B).map g)
  have hcomp : IsIso (g.left ≫ (finiteEtaleOverTerminal B).hom) := inferInstance
  rwa [MorphismProperty.Over.w g] at hcomp

/-- A finite étale cover of a connected scheme whose geometric fibre at some geometric point is a
one-element set is the base itself: its structure morphism is an isomorphism. -/
@[sga "1 V 3.7" "case X′ = Y"]
theorem isIso_hom_of_nonempty_subsingleton_finiteEtaleFiber {B : Scheme.{u}} [ConnectedSpace B]
    (b : GeometricPoint B) (V : FiniteEtaleOver B)
    (hne : Nonempty (finiteEtaleFiber b V)) (hsub : Subsingleton (finiteEtaleFiber b V)) :
    IsIso V.hom := by
  let F := finiteEtaleFiberFunctor b
  let star := finiteEtaleOverTerminal B
  have hstar : IsTerminal star := MorphismProperty.Over.mkIdTerminal _ _
  have : IsIso star.hom := inferInstanceAs (IsIso (𝟙 B))
  have : Subsingleton (F.obj star) :=
    ⟨fun x y ↦ Subtype.ext ((cancel_mono star.hom).mp (x.2.trans y.2.symm))⟩
  let g : V ⟶ star := hstar.from V
  have : IsIso (F.map g) :=
    (isIso_iff_bijective (F.map g)).mpr
      ⟨fun x y _ ↦ hsub.elim x y, fun y ↦ ⟨hne.some, Subsingleton.elim _ _⟩⟩
  have : IsIso g := isIso_of_reflects_iso g F
  exact isIso_hom_of_isIso_to_finiteEtaleOverTerminal g

/-- A finite étale morphism onto a connected scheme whose geometric fibre at some geometric point
is a one-element set is an isomorphism. -/
theorem isIso_of_nonempty_subsingleton_finiteEtaleFiber {B E : Scheme.{u}} [ConnectedSpace B]
    (g : E ⟶ B) (hg : finiteEtale g) (b : GeometricPoint B)
    (hne : Nonempty (finiteEtaleFiber b (MorphismProperty.Over.mk ⊤ g hg)))
    (hsub : Subsingleton (finiteEtaleFiber b (MorphismProperty.Over.mk ⊤ g hg))) : IsIso g :=
  isIso_hom_of_nonempty_subsingleton_finiteEtaleFiber b
    (MorphismProperty.Over.mk ⊤ g hg) hne hsub

/-- The structure morphism of a terminal finite étale cover is an isomorphism. -/
theorem isIso_hom_of_isTerminal_finiteEtaleOver {B : Scheme.{u}} (V : FiniteEtaleOver B)
    (hV : IsTerminal V) : IsIso V.hom := by
  let e : V ≅ finiteEtaleOverTerminal B := hV.uniqueUpToIso (MorphismProperty.Over.mkIdTerminal _ _)
  exact isIso_hom_of_isIso_to_finiteEtaleOverTerminal e.hom

/-! ### The comparison morphism is an isomorphism -/

/-- **A connected finite étale cover which splits over a geometric fibre is the base change of
its Stein image.** Let `f : X ⟶ S` be proper, flat, of finite presentation with geometrically
connected and geometrically reduced fibres, let `v : W ⟶ X` be finite étale with `W` connected,
and let `T` be the Stein image of `v`. If the projection `W ×_X X_s ⟶ X_s` to a geometric fibre
admits a section, then the comparison morphism `W ⟶ T ×_S X` is an isomorphism. -/
theorem isIso_steinComparison_of_section {W X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Flat f]
    [GeometricallyReduced f] [GeometricallyConnected f] (hfp : FinitePresentation f)
    (v : W ⟶ X) [IsFinite v] [Etale v] [ConnectedSpace W] (s : GeometricPoint S)
    (z : GeometricPoint (pullback f s.hom))
    (σ : pullback f s.hom ⟶ pullback v (pullback.fst f s.hom))
    (hσ : σ ≫ pullback.snd v (pullback.fst f s.hom) = 𝟙 _) :
    IsIso (steinComparison f hfp v) := by
  let : LocallyOfFinitePresentation f := hfp.1
  let T := steinImage f hfp v
  let c : W ⟶ T.left := (v ≫ f).toNormalization
  have hc : c ≫ T.hom = v ≫ f :=
    Stacks.SteinFactorization.toNormalization_fromNormalization (v ≫ f)
  let : GeometricallyConnected c :=
    Stacks.SteinFactorization.geometricallyConnected_toNormalization_of_isProper (v ≫ f)
  let : UniversallyClosed c :=
    Stacks.SteinFactorization.universallyClosed_toNormalization (v ≫ f)
  have hTconn : ConnectedSpace ↥T.left := c.surjective.connectedSpace c.continuous
  have : ConnectedSpace ↥((𝟭 Scheme.{u}).obj T.left) := by simpa using hTconn
  let : MorphismProperty.IsStableUnderBaseChangeAlong (P := @GeometricallyConnected) T.hom :=
    ⟨fun pb h ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb h⟩
  let : MorphismProperty.IsStableUnderBaseChangeAlong (P := @Flat) T.hom :=
    ⟨fun pb h ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb h⟩
  let : GeometricallyConnected (pullback.fst T.hom f) :=
    MorphismProperty.pullback_fst T.hom f inferInstance
  let : Flat (pullback.fst T.hom f) := MorphismProperty.pullback_fst T.hom f inferInstance
  have : ConnectedSpace ↥(pullback T.hom f : Scheme.{u}) :=
    GeometricallyConnected.connectedSpace (pullback.fst T.hom f)
      (pullback.fst T.hom f).isOpenMap
  let j := pullback.fst f s.hom
  let k := pullback.snd f s.hom
  let a := pullback.fst v j
  let p := pullback.snd v j
  let : IsFinite p := MorphismProperty.of_isPullback (IsPullback.of_hasPullback v j) inferInstance
  let : Etale p := MorphismProperty.of_isPullback (IsPullback.of_hasPullback v j) inferInstance
  obtain ⟨σ, hσ⟩ : ∃ τ : pullback f s.hom ⟶ pullback v j, τ ≫ p = 𝟙 _ := ⟨σ, hσ⟩
  let cs : pullback v j ⟶ pullback T.hom s.hom :=
    pullback.lift (a ≫ c) (p ≫ k) (by
      simp only [Category.assoc, hc]
      rw [← Category.assoc a, pullback.condition, Category.assoc, pullback.condition])
  have hcs : IsPullback a cs c (pullback.fst T.hom s.hom) := by
    have hout := (IsPullback.of_hasPullback v j).paste_vert (IsPullback.of_hasPullback f s.hom)
    apply IsPullback.of_bot (v₂₁ := pullback.snd T.hom s.hom) (v₂₂ := T.hom)
      (h₃₁ := s.hom) ?_ (pullback.lift_fst (a ≫ c) (p ≫ k) _).symm
      (IsPullback.of_hasPullback T.hom s.hom)
    simpa only [cs, pullback.lift_snd, ← hc] using hout
  let : GeometricallyConnected cs :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hcs inferInstance
  let : UniversallyClosed cs :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hcs inferInstance
  have hcomponents := closedMap_connectedFibres_bijective_connectedComponentsMap cs.base
    cs.continuous cs.isClosedMap cs.isConnected_preimage_singleton
  let g : W ⟶ pullback T.hom f := steinComparison f hfp v
  have hg : finiteEtale g := finiteEtale_steinComparison f hfp v
  let b : GeometricPoint (pullback T.hom f) := z.map (σ ≫ a ≫ g)
  have hgi : g ≫ pullback.snd T.hom f = v := steinComparison_comp_snd f hfp v
  have hgc : g ≫ pullback.fst T.hom f = c := steinComparison_comp_fst f hfp v
  let Q := {q : z.source ⟶ pullback v j //
    q ≫ cs = z.hom ≫ σ ≫ cs ∧ q ≫ p = z.hom}
  have : Subsingleton Q :=
    geometricFiber_pair_subsingleton_of_section cs p σ hσ hcomponents.1 z
  have key : ∀ q : {x : z.source ⟶ W // x ≫ g = z.hom ≫ σ ≫ a ≫ g},
      ∃ t : Q, t.1 ≫ a = q.1 := by
    intro q
    have hq : q.1 ≫ g = z.hom ≫ σ ≫ a ≫ g := q.2
    have hqv : q.1 ≫ v = z.hom ≫ j := by
      have h := hq =≫ pullback.snd T.hom f
      simp only [Category.assoc, hgi] at h
      rw [h, show a ≫ v = p ≫ j from pullback.condition, ← Category.assoc σ, hσ,
        Category.id_comp]
    refine ⟨⟨pullback.lift q.1 z.hom hqv, ?_, pullback.lift_snd _ _ _⟩,
      pullback.lift_fst _ _ _⟩
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, cs, pullback.lift_fst, pullback.lift_fst_assoc, a]
      rw [← hgc, ← Category.assoc q.1, hq]
      simp [Category.assoc, a]
    · simp only [Category.assoc, cs, pullback.lift_snd, pullback.lift_snd_assoc, p]
      rw [← Category.assoc σ, hσ, Category.id_comp]
  have hne : Nonempty {x : z.source ⟶ W // x ≫ g = z.hom ≫ σ ≫ a ≫ g} :=
    ⟨⟨z.hom ≫ σ ≫ a, by rw [Category.assoc, Category.assoc]⟩⟩
  have hsub : Subsingleton {x : z.source ⟶ W // x ≫ g = z.hom ≫ σ ≫ a ≫ g} := by
    refine ⟨fun q q' ↦ Subtype.ext ?_⟩
    obtain ⟨t, ht⟩ := key q
    obtain ⟨t', ht'⟩ := key q'
    rw [← ht, ← ht', Subsingleton.elim t t']
  exact isIso_of_nonempty_subsingleton_finiteEtaleFiber g hg b hne hsub

/-! ### The essential image of base change -/

/-- **A connected finite étale cover of `X` which splits over a geometric fibre comes from the
base**: it is the base change of its Stein image. -/
theorem essImage_finiteEtaleBaseChange_of_isConnected_of_section {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Flat f] [GeometricallyReduced f] [GeometricallyConnected f]
    (hfp : FinitePresentation f) (s : GeometricPoint S)
    (z : GeometricPoint (pullback f s.hom)) (V : FiniteEtaleOver X)
    (hV : PreGaloisCategory.IsConnected V)
    (hsection : ∃ Z : FiniteEtaleOver (pullback f s.hom), Nonempty (IsTerminal Z) ∧
      Nonempty (Z ⟶ (finiteEtaleBaseChange (pullback.fst f s.hom)).obj V)) :
    (finiteEtaleBaseChange f).essImage V := by
  obtain ⟨Z, ⟨hZ⟩, ⟨α⟩⟩ := hsection
  let : IsFinite V.hom := V.prop.1
  let : Etale V.hom := V.prop.2
  have : IsIso Z.hom := isIso_hom_of_isTerminal_finiteEtaleOver Z hZ
  have hVconn : ConnectedSpace ↥V.left := connectedSpace_left_of_isConnected V hV
  have : ConnectedSpace ↥((𝟭 Scheme.{u}).obj V.left) := by simpa using hVconn
  have hα : α.left ≫ ((finiteEtaleBaseChange (pullback.fst f s.hom)).obj V).hom = Z.hom :=
    MorphismProperty.Over.w α
  have hi : (inv Z.hom ≫ α.left) ≫
      ((finiteEtaleBaseChange (pullback.fst f s.hom)).obj V).hom = 𝟙 _ := by
    rw [Category.assoc, hα, IsIso.inv_hom_id]
  have : IsIso (steinComparison f hfp V.hom) :=
    isIso_steinComparison_of_section f hfp V.hom s z (inv Z.hom ≫ α.left) hi
  exact ⟨steinImage f hfp V.hom, ⟨(MorphismProperty.Over.isoMk
    (asIso (steinComparison f hfp V.hom) :
      V.left ≅ pullback (steinImage f hfp V.hom).hom f)
    (steinComparison_comp_snd f hfp V.hom)).symm⟩⟩

/-- **The second condition of [Stacks, Tag 0BS9] for the base-change functors of a proper flat
family.** A finite étale cover of `X` is the base change of a finite étale cover of `S` exactly
when its base change to a geometric fibre `X_s` is a finite coproduct of copies of `X_s`. -/
theorem essImage_finiteEtaleBaseChange_iff_isFiniteCoproductOfTerminal {X S : Scheme.{u}}
    (f : X ⟶ S) [IsProper f] [Flat f] [GeometricallyReduced f] [GeometricallyConnected f]
    (hfp : FinitePresentation f) [ConnectedSpace ↥S] (s : GeometricPoint S)
    (z : GeometricPoint (pullback f s.hom)) (V : FiniteEtaleOver X) :
    (finiteEtaleBaseChange f).essImage V ↔
      IsFiniteCoproductOfTerminal
        ((finiteEtaleBaseChange (pullback.fst f s.hom)).obj V) := by
  let : LocallyOfFinitePresentation f := hfp.1
  have : ConnectedSpace ↥X := GeometricallyConnected.connectedSpace f f.isOpenMap
  have : ConnectedSpace ↥(pullback f s.hom) :=
    connectedSpace_pullback_geometricPoint_of_geometricallyConnected f s
  refine ⟨fun hV ↦ ?_, fun hV ↦ ?_⟩
  · obtain ⟨U, ⟨e⟩⟩ := hV
    exact isFiniteCoproductOfTerminal_of_iso
      ((finiteEtaleBaseChange (pullback.fst f s.hom)).mapIso e)
      (isFiniteCoproductOfTerminal_finiteEtaleBaseChange_geometricFibre f s z U)
  · have hex := exactFunctor_finiteEtaleBaseChange (pullback.fst f s.hom) z
    have : PreservesFiniteLimits (finiteEtaleBaseChange (pullback.fst f s.hom)) := hex.1
    have : PreservesFiniteColimits (finiteEtaleBaseChange f) :=
      (exactFunctor_finiteEtaleBaseChange f (z.map (pullback.fst f s.hom))).2
    exact essImage_of_trivial_of_connected_lifting
      (finiteEtaleFiberFunctor (z.map (pullback.fst f s.hom))) (finiteEtaleFiberFunctor z)
      (finiteEtaleBaseChange f) (finiteEtaleBaseChange (pullback.fst f s.hom))
      (finiteEtaleFiberProjectionIso (pullback.fst f s.hom) z)
      (fun A hA hsec ↦
        essImage_finiteEtaleBaseChange_of_isConnected_of_section f hfp s z A hA hsec)
      V hV

/-! ### The exact sequence -/

/-- **The homotopy sequence of a proper flat family is exact.** Let `f : X ⟶ S` be a flat proper
morphism of finite presentation whose geometric fibres are connected and reduced, let `S` be
connected, let `s` be a geometric point of `S` and let `z` be a geometric point of the geometric
fibre `X_s`. Then

```
π₁(X_s, z) ⟶ π₁(X, z ∘ p) ⟶ π₁(S, z ∘ p ∘ f) ⟶ 1
```

is exact: the second map is surjective, the composite of the two is trivial, and the kernel of
the second map is the smallest closed normal subgroup containing the image of the first. -/
@[stacks 0C0J,
  sga "1 X 1.4" "Surjectivity of π₁(X",
  sga "1 XIII 4.1" "Surjectivity of v",
  sga "1 XIII 4.4" "partial"]
theorem isExactSequence_etaleFundamentalGroupMap_of_properFlat {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] (hfp : FinitePresentation f) [GeometricallyConnected f]
    [GeometricallyReduced f] [ConnectedSpace ↥S] (s : GeometricPoint S)
    (z : GeometricPoint (pullback f s.hom)) :
    letI : LocallyOfFinitePresentation f := hfp.1
    letI : ConnectedSpace ↥X := GeometricallyConnected.connectedSpace f f.isOpenMap
    letI : ConnectedSpace ↥(pullback f s.hom) :=
      connectedSpace_pullback_geometricPoint_of_geometricallyConnected f s
    IsExactSequence (etaleFundamentalGroupMap (pullback.fst f s.hom) z)
      (etaleFundamentalGroupMap f (z.map (pullback.fst f s.hom))) := by
  let : LocallyOfFinitePresentation f := hfp.1
  have : ConnectedSpace ↥X := GeometricallyConnected.connectedSpace f f.isOpenMap
  have : ConnectedSpace ↥(pullback f s.hom) :=
    connectedSpace_pullback_geometricPoint_of_geometricallyConnected f s
  exact isExactSequence_etaleFundamentalGroupMap (pullback.fst f s.hom) f z
    (fullyFaithful_finiteEtaleBaseChange_of_geometricallyConnected f
      (z.map (pullback.fst f s.hom)))
    (essImage_finiteEtaleBaseChange_iff_isFiniteCoproductOfTerminal f hfp s z)

end AlgebraicGeometry

end
