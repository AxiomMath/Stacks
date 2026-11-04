module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceProper
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceRationalPoint
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Dimension.OverField
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.QuasiSeparatedVeryReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeDecency
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.VeryReasonableImpliesReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreDiscreteDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreEquivalences
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreFiniteDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteProperQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActions
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProperSchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation

/-!
# No complete rational curves in a group algebraic space

Let `k` be a field and `G` a separated group algebraic space locally of finite type over `k`.
Every morphism from the projective line `ℙ¹_k` to `G` over `Spec k` is constant: it factors
through a section of the structure morphism of `G`.

## Main definitions

* `AlgebraicGeometry.Space.projectiveLineFunctor`: the functor of points of `ℙ¹_k` restricted
  to the big fppf site over `Spec k`.
* `AlgebraicGeometry.Space.projectiveLinePower`: a power of that functor indexed by a small
  type.
* `AlgebraicGeometry.Space.coordinateProjection`: the projection of a finite power onto the
  coordinates in a finite subset.
* `AlgebraicGeometry.Space.projectiveLineOverBase`: the projective line, viewed over the
  terminal object of presheaves on the site.
* `AlgebraicGeometry.Space.coordinateProjectionUnivIso`: the projection onto *all* `n`
  coordinates, as an isomorphism.

## Main results

* `AlgebraicGeometry.Space.morphism_projectiveLine_eq_constant`: every morphism from `ℙ¹_k` to
  such a `G` is constant, with the contraction step of Stacks 0AEM taken as the hypothesis
  `h0AEMfibres`.
* `AlgebraicGeometry.Space.exists_coordinateProjection_isFinite_of_finite_fibres`: a morphism
  from a finite power of `ℙ¹_k` to a separated algebraic space of finite type over `k` all of
  whose fibres on points are finite is itself finite, so that the factorization of Stacks 0AEM
  holds with the projection onto all `n` coordinates.
* `AlgebraicGeometry.Space.exists_coordinateProjection_isFinite_of_exists_finite_fibres`: a
  factorization through a coordinate projection whose second morphism has finite fibres on
  points can be taken with that second morphism finite.

## Implementation notes

The argument for Stacks 0AEN needs the factorization statement of Stacks 0AEM — a morphism
from a nonempty finite power of `ℙ¹_k` to a separated algebraic space of finite type over `k`
factors through a coordinate projection followed by a *finite* morphism — applied to a morphism
on whose fibres nothing is known in advance. The source proves it in two steps: a contraction
process which produces a factorization through some coordinate projection whose second morphism
has finite fibres over the points of the target, and then the passage from finite fibres to a
finite morphism. The second step is proved here, for a power of `ℙ¹_k` indexed by an arbitrary
finite type, as `AlgebraicGeometry.Space.isFinite_of_finite_fibres`, from which both 0AEM
declarations below follow.

The contraction step is not in this file: in the source it runs through the action of
`(GL_{2,k})^n` on `(ℙ¹_k)^n` and a Zariski-density statement about the orbit of a pair of
points which the source leaves as an exercise, after a reduction to an algebraically closed
field whose details the source omits. All of that is in
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.ProjectiveLineContractionAlgClosed`
and the files it imports, and it is assembled with the statements of this file into the two tags
in `StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.ProjectiveLineFactorization`:
`AlgebraicGeometry.Space.exists_coordinateProjection_isFinite` is Stacks 0AEM and
`AlgebraicGeometry.Space.morphism_projectiveLine_constant` is Stacks 0AEN.  The declarations
here are therefore the components they are assembled from, and carry no tag: the hypothesis
`h0AEMfibres` of `AlgebraicGeometry.Space.morphism_projectiveLine_eq_constant` is exactly that
contraction step — the factorization through a coordinate projection with finite fibres on
points, quantified over every number of coordinates, every target and every morphism — and is
discharged there by
`AlgebraicGeometry.Space.exists_coordinateProjection_finite_fibres`.

One difference with the source should be noted in that hypothesis: the source's contraction
process stops when the fibres over the *`k`-rational* points of the target are finite, and it
passes from there to finite fibres everywhere by the density of the `k`-rational points of the
target, its Stacks 07W4. The form of 07W4 available here,
`AlgebraicGeometry.Space.dense_setOf_class_finiteSeparable_of_isSmooth`, is for a target smooth
over `k`, which the target of 0AEM is not, so `h0AEMfibres` asks for finiteness of the fibres
over every point of the target. It remains strictly weaker than 0AEM, which gives a finite
second morphism and hence finite fibres over every point.

The constant value is produced as a section of the structure morphism of `G`. The proof
applies the factorization to the scheme-theoretic image of `(x, y) ↦ f(x) · f(y)⁻¹`, which is
proper over `Spec k` by Stacks 0AGD. That morphism is trivial on the diagonal, so any
coordinate surviving in the factorization would exhibit `ℙ¹_k` as a retract of a fibre of a
finite morphism, hence make `ℙ¹_k` finite over `Spec k`; its topological Krull dimension is
`1`, so that cannot happen. Thus no coordinate survives, the difference map is constant, and
so is `f`.

## References

* [Stacks Project, Tag 040Z](https://stacks.math.columbia.edu/tag/040Z)
* [Stacks Project, Tag 04NX](https://stacks.math.columbia.edu/tag/04NX)
* [Stacks Project, Tag 0A4X](https://stacks.math.columbia.edu/tag/0A4X)
* [Stacks Project, Tag 0ABY](https://stacks.math.columbia.edu/tag/0ABY)
* [Stacks Project, Tag 0ACK](https://stacks.math.columbia.edu/tag/0ACK)
* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
* [Stacks Project, Tag 0AEN](https://stacks.math.columbia.edu/tag/0AEN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.MonObj

universe w v u

namespace AlgebraicGeometry.Space

/-! ### The projective line on the big fppf site over a field -/

variable (k : Type u) [Field k] (B : BigFppfSite.{u})
  (hk : B.Contains (Spec (CommRingCat.of k)))

/-- The functor of points of the projective line over `k`, restricted to the big fppf site
over `Spec k`. -/
noncomputable abbrev projectiveLineFunctor :
    (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u :=
  (Over.post B.inclusion).op ⋙ yoneda.obj (Over.mk
    (projectiveSpaceOverRing 1 (CommRingCat.of k) ↘ Spec (CommRingCat.of k)))

/-- The power of the projective line indexed by a small type. -/
noncomputable abbrev projectiveLinePower (α : Type v) [Small.{u} α] :
    (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u :=
  ∏ᶜ (fun _ : α => projectiveLineFunctor k B hk)

/-- The projection of a finite power of the projective line onto the coordinates indexed by a
finite subset. -/
noncomputable abbrev coordinateProjection (n : ℕ) (I : Finset (Fin n)) :
    projectiveLinePower k B hk (Fin n) ⟶ projectiveLinePower k B hk I :=
  Pi.map' (fun i : I => (i : Fin n)) (fun _ => 𝟙 _)

/-- The terminal object of presheaves on the big fppf site over `Spec k` is the functor of
points of the identity of `Spec k`. -/
noncomputable def base_isTerminal :
    IsTerminal (yoneda.obj (Over.mk (𝟙 (B.obj hk)))) :=
  (Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 (B.obj hk)))).isTerminalObj yoneda _

/-- The projective line over `k`, viewed over the terminal object of presheaves on the big
fppf site over `Spec k`. -/
noncomputable def projectiveLineOverBase :
    Over (yoneda.obj (Over.mk (𝟙 (B.obj hk)))) :=
  Over.mk ((base_isTerminal k B hk).from (projectiveLinePower k B hk (Fin 1)))

/-- A finite power of the projective line over `k`, viewed over the terminal object of
presheaves on the big fppf site over `Spec k`. -/
noncomputable def projectiveLinePowerOverBase (n : ℕ) :
    Over (yoneda.obj (Over.mk (𝟙 (B.obj hk)))) :=
  Over.mk ((base_isTerminal k B hk).from (projectiveLinePower k B hk (Fin n)))

/-! ### A rational point of the projective line -/

/-- Projective space over a field has a rational point, hence its structure morphism has a
section. -/
private theorem exists_projectiveSpace_section (n : ℕ) :
    ∃ s : Spec (CommRingCat.of k) ⟶ projectiveSpaceOverRing n (CommRingCat.of k),
      s ≫ (projectiveSpaceOverRing n (CommRingCat.of k) ↘ Spec (CommRingCat.of k)) = 𝟙 _ :=
  ⟨pullback.lift (𝟙 _) (allOnesPointAtUniverse (Spec (CommRingCat.of k)) n)
    (terminal.hom_ext _ _), pullback.lift_fst _ _ _⟩

/-- The projective line over a field is not finite over that field: a finite morphism to a
discrete space has discrete source, whereas `ℙ¹_k` has topological Krull dimension `1`. -/
private theorem not_isFinite_projectiveLine :
    ¬ _root_.AlgebraicGeometry.IsFinite
      (projectiveSpaceOverRing 1 (CommRingCat.of k) ↘ Spec (CommRingCat.of k)) := by
  intro hf
  let := hf
  let p := projectiveSpaceOverRing 1 (CommRingCat.of k) ↘ Spec (CommRingCat.of k)
  have hd : _root_.IsDiscrete
      (Set.univ : Set (projectiveSpaceOverRing 1 (CommRingCat.of k))) := by
    simpa only [Set.preimage_univ] using p.isDiscrete_preimage
      (isDiscrete_univ_iff.mpr
        (inferInstance : DiscreteTopology (Spec (CommRingCat.of k))))
  let := isDiscrete_univ_iff.mp hd
  have h := topologicalKrullDim_zero_of_discreteTopology
    (projectiveSpaceOverRing 1 (CommRingCat.of k))
  rw [topologicalKrullDim_projectiveSpaceOverRing] at h
  exact (not_le_of_gt (by norm_num : (0 : WithBot ℕ∞) < 1)) h

include hk in
/-- The projective line over a field is small enough to be an object of any big fppf site
containing `Spec k`: it is proper, hence of finite type and quasi-compact, over `Spec k`. -/
theorem projectiveLine_mem_site :
    B.Contains (projectiveSpaceOverRing 1 (CommRingCat.of k)) := by
  let S := Spec (CommRingCat.of k)
  let P := projectiveSpaceOverRing 1 (CommRingCat.of k)
  let : _root_.AlgebraicGeometry.IsProper (P ↘ S) := inferInstance
  show P.size < B.cutoff
  exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (P ↘ S) hk

/-- The projective line over `k`, as an object of the big fppf site over `Spec k`. -/
noncomputable def projectiveLineSiteObject :
    BigFppfOver B (Spec (CommRingCat.of k)) hk :=
  Over.mk (ObjectProperty.homMk
    (projectiveSpaceOverRing 1 (CommRingCat.of k) ↘ Spec (CommRingCat.of k)) :
    B.obj (projectiveLine_mem_site k B hk) ⟶ B.obj hk)

/-- A finite power of the projective line, as an object of the big fppf site over `Spec k`. -/
noncomputable def projectiveLinePowerSiteObject (n : ℕ) :
    BigFppfOver B (Spec (CommRingCat.of k)) hk := by
  let C := BigFppfOver B (Spec (CommRingCat.of k)) hk
  letI : HasBinaryProducts C := hasBinaryProducts_of_hasTerminal_and_pullbacks C
  letI : HasFiniteProducts C := hasFiniteProducts_of_has_binary_and_terminal
  exact ∏ᶜ (fun _ : Fin n => projectiveLineSiteObject k B hk)

/-! ### Generalities on finite powers and retracts -/

/-- A power indexed by `Fin (n + 1)` is the product of the power indexed by `Fin n` with one
more factor. -/
noncomputable def piFinSuccIso {C : Type u} [Category C]
    [HasFiniteProducts C] (X : C) (n : ℕ) :
    (∏ᶜ fun _ : Fin (n + 1) => X) ≅ (∏ᶜ fun _ : Fin n => X) ⨯ X := by
  let A := ∏ᶜ fun _ : Fin n => X; let L := ∏ᶜ fun _ : Fin (n + 1) => X
  let e : L ⟶ A ⨯ X := prod.lift
    (Pi.lift fun i => Pi.π (fun _ : Fin (n + 1) => X) (Fin.castSucc i))
    (Pi.π (fun _ : Fin (n + 1) => X) (Fin.last n))
  let d : A ⨯ X ⟶ L := Pi.lift (fun i =>
    Fin.lastCases (prod.snd) (fun j => prod.fst ≫ Pi.π _ j) i)
  refine ⟨e, d, ?_, ?_⟩
  · apply Pi.hom_ext; intro i
    cases i using Fin.lastCases <;> simp [e, d, Category.assoc]
  · apply prod.hom_ext
    · apply Pi.hom_ext; intro i
      calc
        ((d ≫ e) ≫ prod.fst) ≫ Pi.π (fun _ : Fin n => X) i =
            d ≫ Pi.π (fun _ : Fin (n + 1) => X) i.castSucc := by
          simp [e, Category.assoc]
        _ = (𝟙 (A ⨯ X) ≫ prod.fst) ≫ Pi.π (fun _ : Fin n => X) i := by simp [d]
    · calc
        (d ≫ e) ≫ prod.snd =
            d ≫ Pi.π (fun _ : Fin (n + 1) => X) (Fin.last n) := by simp [e]
        _ = 𝟙 (A ⨯ X) ≫ prod.snd := by simp [d]

/-- Conjugating a retraction by an isomorphism gives a retraction. -/
private theorem comp_eq_id_of_conj {C : Type*} [Category C] {A A' D : C}
    (e : A ≅ A') (u : A ⟶ D) (v : D ⟶ A) (huv : u ≫ v = 𝟙 A) :
    (e.inv ≫ u) ≫ (v ≫ e.hom) = 𝟙 A' := by
  rw [Category.assoc, ← Category.assoc u v e.hom, huv, Category.id_comp, e.inv_hom_id]

/-! ### Properness and finiteness of powers in the site -/

section SiteProducts

variable (S : Scheme.{u}) (hS : B.Contains S)

/-- The structure morphism of an object of the big fppf site factors through any morphism
out of it. -/
private theorem inclusion_map_hom_eq {X Y : BigFppfOver B S hS} (f : X ⟶ Y) :
    B.inclusion.map X.hom = B.inclusion.map f.left ≫ B.inclusion.map Y.hom := by
  rw [← B.inclusion.map_comp, Over.w]

/-- A product of two objects of the big fppf site which are proper over `S` is proper
over `S`. -/
private theorem isProper_site_product (X Y : BigFppfOver B S hS) [HasBinaryProduct X Y]
    (hX : _root_.AlgebraicGeometry.IsProper (B.inclusion.map X.hom))
    (hY : _root_.AlgebraicGeometry.IsProper (B.inclusion.map Y.hom)) :
    _root_.AlgebraicGeometry.IsProper (B.inclusion.map (X ⨯ Y).hom) := by
  let hpb := (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd X Y)).map B.inclusion
  have hfst : _root_.AlgebraicGeometry.IsProper
      (B.inclusion.map (prod.fst : X ⨯ Y ⟶ X).left) :=
    MorphismProperty.of_isPullback hpb.flip hY
  let := hfst
  let := hX
  rw [inclusion_map_hom_eq B S hS (prod.fst : X ⨯ Y ⟶ X)]; infer_instance

/-- Properness over `S` of an object of the big fppf site is invariant under isomorphism. -/
private theorem isProper_site_of_iso {X Y : BigFppfOver B S hS} (e : X ≅ Y)
    (hY : _root_.AlgebraicGeometry.IsProper (B.inclusion.map Y.hom)) :
    _root_.AlgebraicGeometry.IsProper (B.inclusion.map X.hom) := by
  let := hY
  let : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  rw [inclusion_map_hom_eq B S hS e.hom]; infer_instance

/-- A finite power of an object of the big fppf site which is proper over `S` is proper
over `S`. -/
private theorem isProper_site_power [HasFiniteProducts (BigFppfOver B S hS)]
    (X : BigFppfOver B S hS)
    (hX : _root_.AlgebraicGeometry.IsProper (B.inclusion.map X.hom)) (n : ℕ) :
    _root_.AlgebraicGeometry.IsProper
      (B.inclusion.map (∏ᶜ fun _ : Fin n => X).hom) := by
  induction n with
  | zero =>
    have ht : IsTerminal (∏ᶜ fun _ : Fin 0 => X) :=
      IsTerminal.ofUniqueHom (fun _ => Pi.lift fun i => Fin.elim0 i)
        (fun _ _ => Pi.hom_ext _ _ fun i => Fin.elim0 i)
    apply isProper_site_of_iso B S hS (ht.uniqueUpToIso Over.mkIdTerminal)
    show _root_.AlgebraicGeometry.IsProper (B.inclusion.map (𝟙 (B.obj hS)))
    rw [CategoryTheory.Functor.map_id]; infer_instance
  | succ n ih =>
    exact isProper_site_of_iso B S hS (piFinSuccIso X n)
      (isProper_site_product B S hS _ X ih hX)

/-- If an object `X` of the big fppf site is a retract of the source of a finite morphism whose
composite with that retraction lands in a fibre over the base, then `X` is finite over `S`.

The retraction exhibits `X` as a closed subspace of the base change, which is finite
over `S`. -/
private theorem isFinite_of_retract_in_finite_fiber [IsAffine S] (X : BigFppfOver B S hS)
    {Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Y ⟶ Z) (hg : IsFinite B S hS g)
    (d : yoneda.obj X ⟶ Y) (r : Y ⟶ yoneda.obj X) (hdr : d ≫ r = 𝟙 _)
    (c : yoneda.obj (Over.mk (𝟙 (B.obj hS))) ⟶ Z)
    (hdg : d ≫ g = yoneda.map (Over.homMk X.hom) ≫ c) :
    _root_.AlgebraicGeometry.IsFinite (B.inclusion.map X.hom) := by
  obtain ⟨V, p, i, _, hp, hpb⟩ := hg (Over.mk (𝟙 (B.obj hS)))
    (inferInstance : IsAffine S) c
  let l := hpb.lift d (yoneda.map (Over.homMk X.hom)) hdg
  let a : X ⟶ V := yoneda.preimage l
  let b : V ⟶ X := yoneda.preimage (i ≫ r)
  have hab : a ≫ b = 𝟙 X := by
    apply yoneda.map_injective
    simp only [Functor.map_comp, CategoryTheory.Functor.map_id, a, b, yoneda.map_preimage,
      ← Category.assoc]
    rw [show l ≫ i = d from hpb.lift_fst _ _ _, hdr]
  let F := BigFppfOver.toScheme B S hS
  have hp' : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map V.hom) := by
    have he : p.left = V.hom := by simpa using p.w
    simpa only [F, BigFppfOver.toScheme, Functor.comp_map, Over.forget_map, he] using hp
  let := hp'
  have hb : _root_.AlgebraicGeometry.IsSeparated (F.map b) := by
    have : _root_.AlgebraicGeometry.IsSeparated (F.map b ≫ B.inclusion.map X.hom) := by
      change _root_.AlgebraicGeometry.IsSeparated
        (B.inclusion.map b.left ≫ B.inclusion.map X.hom)
      rw [← inclusion_map_hom_eq B S hS b]; infer_instance
    exact _root_.AlgebraicGeometry.IsSeparated.of_comp (F.map b) (B.inclusion.map X.hom)
  let := hb
  have : _root_.AlgebraicGeometry.IsClosedImmersion (F.map a ≫ F.map b) := by
    rw [← F.map_comp, hab, F.map_id]; infer_instance
  have : _root_.AlgebraicGeometry.IsClosedImmersion (F.map a) :=
    _root_.AlgebraicGeometry.IsClosedImmersion.of_comp _ (F.map b)
  rw [inclusion_map_hom_eq B S hS a]
  exact (inferInstance : _root_.AlgebraicGeometry.IsFinite (F.map a ≫ B.inclusion.map V.hom))

end SiteProducts

/-! ### Comparing the restricted functor with the represented one -/

/-- The restricted functor of points of the projective line is represented by the
corresponding object of the big fppf site over `Spec k`. -/
noncomputable def projectiveLineRestrictedYonedaIso :
    projectiveLineFunctor k B hk ≅ yoneda.obj (projectiveLineSiteObject k B hk) := by
  let F : BigFppfOver B (Spec (CommRingCat.of k)) hk ⥤ Over (Spec (CommRingCat.of k)) :=
    Over.post (X := B.obj hk) B.inclusion
  letI : B.inclusion.Full := by infer_instance
  letI : B.inclusion.Faithful := by infer_instance
  let inclFF : B.inclusion.FullyFaithful :=
    Functor.FullyFaithful.ofFullyFaithful B.inclusion
  let FF : F.FullyFaithful := inclFF.over (X := B.obj hk)
  refine NatIso.ofComponents (fun X => Equiv.toIso
    (FF.homEquiv (X := X.unop) (Y := projectiveLineSiteObject k B hk)).symm) ?_
  intro X Y f; ext g
  change F.obj X.unop ⟶ F.obj (projectiveLineSiteObject k B hk) at g
  apply FF.map_injective
  change F.map (FF.preimage (F.map f.unop ≫ g)) = F.map (f.unop ≫ FF.preimage g)
  simp

/-- A finite power of the restricted functor of points of the projective line is represented
by the corresponding finite power in the big fppf site over `Spec k`. -/
noncomputable def projectiveLinePowerRepresentationIso (n : ℕ) :
    projectiveLinePower k B hk (Fin n) ≅
      yoneda.obj (projectiveLinePowerSiteObject k B hk n) := by
  let C := BigFppfOver B (Spec (CommRingCat.of k)) hk
  letI : HasBinaryProducts C := hasBinaryProducts_of_hasTerminal_and_pullbacks C
  letI : HasFiniteProducts C := hasFiniteProducts_of_has_binary_and_terminal
  let D : Discrete (Fin n) ⥤ C := Discrete.functor fun _ => projectiveLineSiteObject k B hk
  letI : PreservesLimit D yoneda := inferInstance
  let eprod : (∏ᶜ fun _ : Fin n => projectiveLineSiteObject k B hk) ≅ limit D :=
    Pi.isoLimit D
  let e1 : projectiveLinePower k B hk (Fin n) ≅
      ∏ᶜ fun _ : Fin n => yoneda.obj (projectiveLineSiteObject k B hk) :=
    Pi.mapIso (fun _ => projectiveLineRestrictedYonedaIso k B hk)
  let e2 : (∏ᶜ fun _ : Fin n => yoneda.obj (projectiveLineSiteObject k B hk)) ≅
      yoneda.obj (∏ᶜ fun _ : Fin n => projectiveLineSiteObject k B hk) := by
    let eYoneda := preservesLimitIso yoneda D
    exact asIso ((Pi.isoLimit (D ⋙ yoneda)).hom ≫ eYoneda.inv ≫ yoneda.map eprod.inv)
  exact e1 ≪≫ e2

/-! ### Coordinates of a finite power over the base -/

/-- The `i`-th coordinate of a finite power of the projective line, over the base. -/
private noncomputable def projectiveLinePowerCoordinate (n : ℕ) (i : Fin n) :
    projectiveLinePowerOverBase k B hk n ⟶ projectiveLineOverBase k B hk :=
  Over.homMk
    (Pi.lift (fun _ : Fin 1 => Pi.π (fun _ : Fin n => projectiveLineFunctor k B hk) i))
    ((base_isTerminal k B hk).hom_ext _ _)

/-- The morphism to the square of the projective line with prescribed coordinates. -/
private noncomputable def pairCoordinates
    (a b : projectiveLineOverBase k B hk ⟶ projectiveLineOverBase k B hk) :
    projectiveLineOverBase k B hk ⟶ projectiveLinePowerOverBase k B hk 2 :=
  Over.homMk (Pi.lift fun i : Fin 2 =>
    (if i = 0 then a.left else b.left) ≫
      Pi.π (fun _ : Fin 1 => projectiveLineFunctor k B hk) 0)
    ((base_isTerminal k B hk).hom_ext _ _)

/-- The coordinates of `AlgebraicGeometry.Space.pairCoordinates` are the prescribed ones. -/
private theorem pairCoordinates_proj
    (a b : projectiveLineOverBase k B hk ⟶ projectiveLineOverBase k B hk) (j : Fin 2) :
    pairCoordinates k B hk a b ≫ projectiveLinePowerCoordinate k B hk 2 j =
      if j = 0 then a else b := by
  fin_cases j <;> apply Over.OverMorphism.ext <;> apply Pi.hom_ext <;> intro i
  · show (Pi.lift _ ≫ Pi.lift (fun _ : Fin 1 => Pi.π _ 0)) ≫ Pi.π _ i = _
    fin_cases i
    simp [Category.assoc]
    rfl
  · show (Pi.lift _ ≫ Pi.lift (fun _ : Fin 1 => Pi.π _ 1)) ≫ Pi.π _ i = _
    fin_cases i
    simp [Category.assoc]
    rfl

/-- The structure morphism of a finite power of the projective line, as a morphism in the big
fppf site, is proper. -/
private theorem isProper_yoneda_map_power (n : ℕ) :
    IsProper B (Spec (CommRingCat.of k)) hk
      (yoneda.map (Over.homMk (projectiveLinePowerSiteObject k B hk n).hom :
        projectiveLinePowerSiteObject k B hk n ⟶ Over.mk (𝟙 (B.obj hk)))) := by
  let : HasBinaryProducts (BigFppfOver B (Spec (CommRingCat.of k)) hk) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let : HasFiniteProducts (BigFppfOver B (Spec (CommRingCat.of k)) hk) :=
    hasFiniteProducts_of_has_binary_and_terminal
  exact isProper_yoneda_map B (Spec (CommRingCat.of k)) hk _
    (isProper_site_power B (Spec (CommRingCat.of k)) hk (projectiveLineSiteObject k B hk)
      (inferInstance : _root_.AlgebraicGeometry.IsProper
        (projectiveSpaceOverRing 1 (CommRingCat.of k) ↘ Spec (CommRingCat.of k))) n)

/-- A separated morphism between algebraic spaces over `Spec k` is decent. -/
private theorem isDecent_of_isSeparated {X Y : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤
      Type u} (hX : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk X)
    (hY : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk Y) (f : X ⟶ Y)
    (hf : IsSeparated B (Spec (CommRingCat.of k)) hk f) :
    IsDecent B (Spec (CommRingCat.of k)) hk f :=
  isDecent_of_isReasonable B (Spec (CommRingCat.of k)) hk hX hY f
    (isReasonable_of_isVeryReasonable B (Spec (CommRingCat.of k)) hk hX hY
      (isVeryReasonable_of_isQuasiSeparated B (Spec (CommRingCat.of k)) hk hX hY
        (isQuasiSeparated_of_isSeparated B (Spec (CommRingCat.of k)) hk hf)))

/-- Composing a finite morphism with an isomorphism on the left gives a finite morphism. -/
private theorem isFinite_iso_hom_comp {X Y Z : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤
      Type u} (e : X ≅ Y) {g : Y ⟶ Z} (hg : IsFinite B (Spec (CommRingCat.of k)) hk g) :
    IsFinite B (Spec (CommRingCat.of k)) hk (e.hom ≫ g) :=
  isFinite_comp B (Spec (CommRingCat.of k)) hk
    (isFinite_of_isClosedImmersion B (Spec (CommRingCat.of k)) hk e.hom
      (isClosedImmersion_of_isIso B (Spec (CommRingCat.of k)) hk e.hom)) hg

/-! ### Finite fibres make a morphism out of a power of the projective line finite -/

section FiniteFibres

attribute [local instance] pointTopology

/-- Reindexing a power of the projective line along an equivalence of the index types. -/
noncomputable def projectiveLinePowerReindexIso {α : Type v} [Small.{u} α]
    {β : Type w} [Small.{u} β] (e : α ≃ β) :
    projectiveLinePower k B hk α ≅ projectiveLinePower k B hk β :=
  Pi.whiskerEquiv (f := fun _ : α => projectiveLineFunctor k B hk)
    (g := fun _ : β => projectiveLineFunctor k B hk) e fun _ ↦ Iso.refl _

/-- A morphism `w` from the power of the projective line indexed by `Fin n` to an algebraic
space `Z` which is separated over `k` and all of whose fibres on points are finite is finite.

The source `(ℙ¹_k)^n` is represented by a finite power of the projective line in the big fppf
site, which is proper over `Spec k`, so `w` is proper by part (2) of Stacks 04NX, `Z` being
separated over `k`. Properness makes `w` separated, hence quasi-separated, hence very
reasonable, reasonable and finally decent (Stacks 03M5), and makes both `(ℙ¹_k)^n` and `Z`
decent algebraic spaces (Stacks 0ABY). Finiteness of a set-theoretic fibre then upgrades to
finiteness of the point set of the corresponding field fibre, which is discrete, which in turn
means that `w` is quasi-finite at every point above it — these are the implications
(1) ⇒ (4) ⇒ (5) ⇒ (8) of Stacks 0ACK. Every point of `|Z|` is represented by a field-valued
point, so `w` is quasi-finite at every point of its source, hence locally quasi-finite by
Stacks 040Z and finite by Stacks 0A4X. -/
private theorem isFinite_of_finite_fibres_fin (n : ℕ)
    (Z : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u)
    (hZ : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk Z)
    (z : Z ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk))))
    (hsep : IsSeparated B (Spec (CommRingCat.of k)) hk z)
    (w : projectiveLinePower k B hk (Fin n) ⟶ Z)
    (hfib : ∀ y : points B (Spec (CommRingCat.of k)) hk Z,
      {x : points B (Spec (CommRingCat.of k)) hk (projectiveLinePower k B hk (Fin n)) |
        pointsMap B (Spec (CommRingCat.of k)) hk (projectiveLinePower k B hk (Fin n)) w x =
          y}.Finite) :
    IsFinite B (Spec (CommRingCat.of k)) hk w := by
  classical
  let : HasBinaryProducts (BigFppfOver B (Spec (CommRingCat.of k)) hk) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let : HasFiniteProducts (BigFppfOver B (Spec (CommRingCat.of k)) hk) :=
    hasFiniteProducts_of_has_binary_and_terminal
  let X := projectiveLinePower k B hk (Fin n)
  let XO := projectiveLinePowerSiteObject k B hk n
  let e : X ≅ yoneda.obj XO := projectiveLinePowerRepresentationIso k B hk n
  let pX : XO ⟶ Over.mk (𝟙 (B.obj hk)) := Over.homMk XO.hom
  have hT : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk
      (yoneda.obj (Over.mk (𝟙 (B.obj hk)))) :=
    isAlgebraicSpace_yoneda B (Spec (CommRingCat.of k)) hk _
  have hX : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk X :=
    isAlgebraicSpace_of_iso B (Spec (CommRingCat.of k)) hk e.symm
      (isAlgebraicSpace_yoneda B (Spec (CommRingCat.of k)) hk XO)
  have hpX : IsProper B (Spec (CommRingCat.of k)) hk (yoneda.map pX) :=
    isProper_yoneda_map_power k B hk n
  have hbase : w ≫ z = e.hom ≫ yoneda.map pX := (base_isTerminal k B hk).hom_ext _ _
  have hwz : IsProper B (Spec (CommRingCat.of k)) hk (w ≫ z) := by
    rw [hbase]
    exact (isProper_isIso_comp_iff B (Spec (CommRingCat.of k)) hk e.hom (yoneda.map pX)).2 hpX
  have hwproper : IsProper B (Spec (CommRingCat.of k)) hk w :=
    isProper_of_comp_of_isSeparated B (Spec (CommRingCat.of k)) hk hX hZ hT w z hwz hsep
  have hwlft : IsLocallyOfFiniteType B (Spec (CommRingCat.of k)) hk w := hwproper.2.1.1
  have hwdecent : IsDecent B (Spec (CommRingCat.of k)) hk w :=
    isDecent_of_isSeparated k B hk hX hZ w hwproper.1
  have hzdecent : IsDecent B (Spec (CommRingCat.of k)) hk z :=
    isDecent_of_isSeparated k B hk hZ hT z hsep
  have hZdec : IsDecentSpace B (Spec (CommRingCat.of k)) hk Z :=
    isDecentSpace_of_isDecent B (Spec (CommRingCat.of k)) hk hZ hT z
      (isDecentSpace_yoneda B (Spec (CommRingCat.of k)) hk _) hzdecent
  have hXdec : IsDecentSpace B (Spec (CommRingCat.of k)) hk X :=
    isDecentSpace_of_isDecent B (Spec (CommRingCat.of k)) hk hX hZ w hZdec hwdecent
  have hlqf : IsLocallyQuasiFinite B (Spec (CommRingCat.of k)) hk w := by
    refine (isLocallyQuasiFinite_iff_forall_isQuasiFiniteAt B (Spec (CommRingCat.of k)) hk
      hX hZ w).2 fun x ↦ ?_
    obtain ⟨p, hp⟩ := Quot.exists_rep (pointsMap B (Spec (CommRingCat.of k)) hk X w x)
    have hx : x ∈ setFibre B (Spec (CommRingCat.of k)) hk w p := hp.symm
    have hfieldfin := finite_univ_points_fieldFibre_of_finite_setFibre_of_isDecent B
      (Spec (CommRingCat.of k)) hk hX hZ w p hwlft hXdec hZdec
      (hfib (p.class B (Spec (CommRingCat.of k)) hk Z))
    exact (isDiscreteFieldFibrePoints_iff_isQuasiFiniteAboveFieldValuedPoint B
        (Spec (CommRingCat.of k)) hk hX hZ hwlft p).mp
      (discreteTopology_points_fieldFibre_of_finite_of_isDecent B (Spec (CommRingCat.of k)) hk
        hX hZ w p hwlft hwdecent hfieldfin) x hx
  exact isFinite_of_isProper_of_isLocallyQuasiFinite B (Spec (CommRingCat.of k)) hk hX hZ w
    hwproper hlqf

/-- A morphism `w` from the power of the projective line indexed by a finite type `α` to an
algebraic space `Z` which is separated over `k` and all of whose fibres on points are finite is
finite: reindex the power by `Fin (Nat.card α)`, which multiplies `w` by an isomorphism and so
changes neither the fibres nor the finiteness, and apply the case of an index `Fin n`. -/
private theorem isFinite_of_finite_fibres (α : Type v) [Small.{u} α] [Finite α]
    (Z : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u)
    (hZ : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk Z)
    (z : Z ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk))))
    (hsep : IsSeparated B (Spec (CommRingCat.of k)) hk z)
    (w : projectiveLinePower k B hk α ⟶ Z)
    (hfib : ∀ y : points B (Spec (CommRingCat.of k)) hk Z,
      {x : points B (Spec (CommRingCat.of k)) hk (projectiveLinePower k B hk α) |
        pointsMap B (Spec (CommRingCat.of k)) hk (projectiveLinePower k B hk α) w x =
          y}.Finite) :
    IsFinite B (Spec (CommRingCat.of k)) hk w := by
  let e : projectiveLinePower k B hk α ≅ projectiveLinePower k B hk (Fin (Nat.card α)) :=
    projectiveLinePowerReindexIso k B hk (Finite.equivFin α)
  have hcomp := pointsMap_comp B (Spec (CommRingCat.of k)) hk
    (projectiveLinePower k B hk (Fin (Nat.card α))) e.inv e.hom
  rw [e.inv_hom_id, pointsMap_id] at hcomp
  have hinj : Function.Injective (pointsMap B (Spec (CommRingCat.of k)) hk
      (projectiveLinePower k B hk (Fin (Nat.card α))) e.inv) :=
    (Function.leftInverse_iff_comp.2 hcomp.symm).injective
  have hfib' : ∀ y : points B (Spec (CommRingCat.of k)) hk Z,
      {x : points B (Spec (CommRingCat.of k)) hk
          (projectiveLinePower k B hk (Fin (Nat.card α))) |
        pointsMap B (Spec (CommRingCat.of k)) hk
          (projectiveLinePower k B hk (Fin (Nat.card α))) (e.inv ≫ w) x = y}.Finite := by
    intro y
    have hset : {x : points B (Spec (CommRingCat.of k)) hk
          (projectiveLinePower k B hk (Fin (Nat.card α))) |
        pointsMap B (Spec (CommRingCat.of k)) hk
          (projectiveLinePower k B hk (Fin (Nat.card α))) (e.inv ≫ w) x = y} =
        pointsMap B (Spec (CommRingCat.of k)) hk
            (projectiveLinePower k B hk (Fin (Nat.card α))) e.inv ⁻¹'
          {x : points B (Spec (CommRingCat.of k)) hk (projectiveLinePower k B hk α) |
            pointsMap B (Spec (CommRingCat.of k)) hk (projectiveLinePower k B hk α) w x = y} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_preimage,
        pointsMap_comp B (Spec (CommRingCat.of k)) hk _ e.inv w, Function.comp_apply]
    rw [hset]
    exact (hfib y).preimage hinj.injOn
  have hfin := isFinite_of_finite_fibres_fin k B hk (Nat.card α) Z hZ z hsep (e.inv ≫ w) hfib'
  rw [show w = e.hom ≫ e.inv ≫ w from (e.hom_inv_id_assoc w).symm]
  exact isFinite_iso_hom_comp k B hk e hfin

end FiniteFibres

/-! ### No complete rational curves -/

/-- Let `k` be a field and `G` a separated group algebraic space locally of finite type over
`k`. Every morphism from the projective line over `k` to `G` over `Spec k` is constant: it
factors through a section of the structure morphism of `G`.

Only the contraction step of Stacks 0AEM is taken as a hypothesis, as `h0AEMfibres`: that the
morphism factors through *some* coordinate projection by a morphism whose fibres on points are
finite. That such a second morphism is then finite — the rest of 0AEM — is proved here, as
`AlgebraicGeometry.Space.isFinite_of_finite_fibres`.

This is the component carrying no tag; Stacks 0AEN itself, with `h0AEMfibres` discharged, is
`AlgebraicGeometry.Space.morphism_projectiveLine_constant`. -/
theorem morphism_projectiveLine_eq_constant
    (G : GroupAlgebraicSpace B (Spec (CommRingCat.of k)) hk
      (yoneda.obj (Over.mk (𝟙 (B.obj hk))))
      (isAlgebraicSpace_yoneda B (Spec (CommRingCat.of k)) hk _))
    (hsep : IsSeparatedOver B (Spec (CommRingCat.of k)) hk G.obj.X.left)
    (hft : IsLocallyOfFiniteType B (Spec (CommRingCat.of k)) hk G.obj.X.hom)
    (h0AEMfibres : ∀ n : ℕ, 0 < n →
      ∀ Z : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u,
        IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk Z →
        ∀ z : Z ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk))),
          IsSeparated B (Spec (CommRingCat.of k)) hk z →
          IsFiniteType B (Spec (CommRingCat.of k)) hk z →
          ∀ w : projectiveLinePower k B hk (Fin n) ⟶ Z,
            ∃ (I : Finset (Fin n)) (g : projectiveLinePower k B hk I ⟶ Z),
              w = coordinateProjection k B hk n I ≫ g ∧
                ∀ y : points B (Spec (CommRingCat.of k)) hk Z,
                  {x : points B (Spec (CommRingCat.of k)) hk
                      (projectiveLinePower k B hk I) |
                    pointsMap B (Spec (CommRingCat.of k)) hk
                      (projectiveLinePower k B hk I) g x = y}.Finite)
    (f : projectiveLineOverBase k B hk ⟶ G.obj.X) :
    ∃ c : yoneda.obj (Over.mk (𝟙 (B.obj hk))) ⟶ G.obj.X.left,
      c ≫ G.obj.X.hom = 𝟙 _ ∧
        f.left = (projectiveLineOverBase k B hk).hom ≫ c := by
  classical
  let : HasBinaryProducts (BigFppfOver B (Spec (CommRingCat.of k)) hk) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let : HasFiniteProducts (BigFppfOver B (Spec (CommRingCat.of k)) hk) :=
    hasFiniteProducts_of_has_binary_and_terminal
  let L := projectiveLineOverBase k B hk
  let T := yoneda.obj (Over.mk (𝟙 (B.obj hk)))
  let ht := base_isTerminal k B hk
  let t : L ⟶ Over.mk (𝟙 T) := Over.homMk L.hom
  let eL := projectiveLinePowerRepresentationIso k B hk 1
  let X1 := projectiveLinePowerSiteObject k B hk 1
  let e1 : X1 ≅ projectiveLineSiteObject k B hk := productUniqueIso _
  obtain ⟨s0, hs0⟩ := exists_projectiveSpace_section k 1
  let sSite : Over.mk (𝟙 (B.obj hk)) ⟶ projectiveLineSiteObject k B hk :=
    Over.homMk (ObjectProperty.homMk s0) (by
      apply ObjectProperty.hom_ext
      exact hs0)
  let s : Over.mk (𝟙 T) ⟶ L := Over.homMk
    (yoneda.map (sSite ≫ e1.inv) ≫ eL.inv) (ht.hom_ext _ _)
  let d := pairCoordinates k B hk (𝟙 L) (𝟙 L)
  let m := pairCoordinates k B hk (𝟙 L) (t ≫ s)
  let q : projectiveLinePowerOverBase k B hk 2 ⟶ G.obj.X :=
    (projectiveLinePowerCoordinate k B hk 2 0 ≫ f) *
      (projectiveLinePowerCoordinate k B hk 2 1 ≫ f)⁻¹
  have hd : d ≫ q = 1 := by
    simp [q, d, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, pairCoordinates_proj]
  let X := projectiveLinePowerSiteObject k B hk 2
  let e := projectiveLinePowerRepresentationIso k B hk 2
  let hX := isAlgebraicSpace_yoneda B (Spec (CommRingCat.of k)) hk X
  let hT := isAlgebraicSpace_yoneda B (Spec (CommRingCat.of k)) hk (Over.mk (𝟙 (B.obj hk)))
  let pX : X ⟶ Over.mk (𝟙 (B.obj hk)) := Over.homMk X.hom
  have hp : IsProper B (Spec (CommRingCat.of k)) hk (yoneda.map pX) :=
    isProper_yoneda_map_power k B hk 2
  have hsep' : IsSeparated B (Spec (CommRingCat.of k)) hk G.obj.X.hom :=
    (isSeparatedOver_iff_isSeparated_of_isTerminal B (Spec (CommRingCat.of k)) hk ht
      G.obj.X.hom).mp hsep
  let F := e.inv ≫ q.left
  let Zsub := schemeTheoreticImageSubfunctor B (Spec (CommRingCat.of k)) hk F
  let qZ := toSchemeTheoreticImage B (Spec (CommRingCat.of k)) hk F
  let q2Z := e.hom ≫ qZ
  have hZalg : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk Zsub.toFunctor :=
    (isClosedSubspace_schemeTheoreticImageSubfunctor B (Spec (CommRingCat.of k)) hk F
      G.property).1
  have hqZ : q2Z ≫ Zsub.ι = q.left := by
    have hassoc : q2Z ≫ Zsub.ι = e.hom ≫ (qZ ≫ Zsub.ι) := Category.assoc _ _ _
    rw [hassoc, toSchemeTheoreticImage_ι]
    exact e.hom_inv_id_assoc q.left
  have hz := isProper_schemeTheoreticImageSubfunctor_inclusion_comp B
    (Spec (CommRingCat.of k)) hk hX G.property hT F (yoneda.map pX) G.obj.X.hom
    (ht.hom_ext _ _) hp hsep' hft
  obtain ⟨I, g, hfac, hgfib⟩ := h0AEMfibres 2 (by decide) Zsub.toFunctor hZalg
    (Zsub.ι ≫ G.obj.X.hom) hz.1 hz.2.1 q2Z
  have hg : IsFinite B (Spec (CommRingCat.of k)) hk g :=
    isFinite_of_finite_fibres k B hk I Zsub.toFunctor hZalg (Zsub.ι ≫ G.obj.X.hom) hz.1 g hgfib
  have hI : I = ∅ := by
    by_contra hi
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hi
    let δ := eL.inv ≫ d.left ≫ coordinateProjection k B hk 2 I
    let r := Pi.lift (fun _ : Fin 1 =>
      Pi.π (fun _ : I => projectiveLineFunctor k B hk) ⟨j, hj⟩) ≫ eL.hom
    have hcoord : coordinateProjection k B hk 2 I ≫
        Pi.lift (fun _ : Fin 1 =>
          Pi.π (fun _ : I => projectiveLineFunctor k B hk) ⟨j, hj⟩) =
        (projectiveLinePowerCoordinate k B hk 2 j).left := by
      apply Pi.hom_ext; intro i
      show (Pi.map' (fun i : I => (i : Fin 2))
          (fun _ => 𝟙 (projectiveLineFunctor k B hk)) ≫
        Pi.lift (fun _ : Fin 1 =>
          Pi.π (fun _ : I => projectiveLineFunctor k B hk) ⟨j, hj⟩)) ≫
        Pi.π (fun _ : Fin 1 => projectiveLineFunctor k B hk) i =
        (Pi.lift (fun _ : Fin 1 =>
          Pi.π (fun _ : Fin 2 => projectiveLineFunctor k B hk) j)) ≫
        Pi.π (fun _ : Fin 1 => projectiveLineFunctor k B hk) i
      simp
    have hdj : d ≫ projectiveLinePowerCoordinate k B hk 2 j = 𝟙 L := by
      simpa [d] using pairCoordinates_proj k B hk (𝟙 L) (𝟙 L) j
    have hdjleft : d.left ≫ (projectiveLinePowerCoordinate k B hk 2 j).left = 𝟙 L.left := by
      simpa using congrArg Over.Hom.left hdj
    have hu : (d.left ≫ coordinateProjection k B hk 2 I) ≫
        Pi.lift (fun _ : Fin 1 =>
          Pi.π (fun _ : I => projectiveLineFunctor k B hk) ⟨j, hj⟩) = 𝟙 _ :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun z => d.left ≫ z) hcoord).trans hdjleft)
    have hdr : δ ≫ r = 𝟙 _ := comp_eq_id_of_conj eL _ _ hu
    let cZ := s.left ≫ d.left ≫ q2Z
    have he : d.left ≫ q.left = L.hom ≫ s.left ≫ d.left ≫ q.left :=
      show (d ≫ q).left = (t ≫ s ≫ d ≫ q).left by simp only [hd, MonObj.comp_one]
    have hA : (d.left ≫ q2Z) ≫ Zsub.ι = d.left ≫ q.left :=
      (Category.assoc _ _ _).trans (congrArg (fun z => d.left ≫ z) hqZ)
    have hB : (L.hom ≫ cZ) ≫ Zsub.ι = L.hom ≫ s.left ≫ d.left ≫ q.left :=
      (Category.assoc _ _ _).trans
        (congrArg (fun z => L.hom ≫ z)
          ((Category.assoc _ _ _).trans (congrArg (fun z => s.left ≫ z) hA)))
    have hdconst : d.left ≫ q2Z = L.hom ≫ cZ :=
      (cancel_mono Zsub.ι).mp (hA.trans (he.trans hB.symm))
    have ht' : eL.inv ≫ L.hom = yoneda.map (Over.homMk X1.hom) := ht.hom_ext _ _
    have hδ : δ ≫ g = yoneda.map (Over.homMk X1.hom) ≫ cZ :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun z => eL.inv ≫ z)
            ((Category.assoc _ _ _).trans
              ((congrArg (fun z => d.left ≫ z) hfac.symm).trans hdconst))).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ cZ) ht')))
    have hfinite := isFinite_of_retract_in_finite_fiber B (Spec (CommRingCat.of k)) hk X1
      g hg δ r hdr cZ hδ
    have hfiniteP : _root_.AlgebraicGeometry.IsFinite
        (B.inclusion.map (projectiveLineSiteObject k B hk).hom) := by
      let := hfinite
      let : IsIso e1.inv.left := (Over.forget _).map_isIso e1.inv
      rw [inclusion_map_hom_eq B _ hk e1.inv]; infer_instance
    exact not_isFinite_projectiveLine k hfiniteP
  have hπ : m.left ≫ coordinateProjection k B hk 2 I =
      d.left ≫ coordinateProjection k B hk 2 I :=
    Pi.hom_ext _ _ fun i => False.elim (by simpa [hI] using i.property)
  have key : ∀ a : L.left ⟶ projectiveLinePower k B hk (Fin 2),
      a ≫ q.left = ((a ≫ coordinateProjection k B hk 2 I) ≫ g) ≫ Zsub.ι := fun a => by
    rw [← hqZ, hfac]
    simp only [Category.assoc]
  have hmq : m ≫ q = d ≫ q := by
    apply Over.OverMorphism.ext
    show m.left ≫ q.left = d.left ≫ q.left
    exact (key m.left).trans
      ((congrArg (fun z => (z ≫ g) ≫ Zsub.ι) hπ).trans (key d.left).symm)
  have hfeq : f = t ≫ s ≫ f := by
    have h1 : f * (t ≫ s ≫ f)⁻¹ = 1 := by
      have hm := hmq.trans hd
      simp only [q, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, m,
        pairCoordinates_proj] at hm
      simp only [ite_true, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)] at hm
      rw [Category.id_comp] at hm
      exact hm
    exact mul_inv_eq_one.mp h1
  exact ⟨s.left ≫ f.left, ht.hom_ext _ _, congrArg Over.Hom.left hfeq⟩

/-- `AlgebraicGeometry.Space.morphism_projectiveLine_eq_constant` with the projective line,
its powers and the group algebraic space written out in full. -/
example
    (G : ObjectProperty.FullSubcategory
      ((fun G => IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk G.X.left :
        ObjectProperty (Grp (Over (yoneda.obj (Over.mk (𝟙 (B.obj hk)))))))))
    (hsep : IsClosedImmersion B (Spec (CommRingCat.of k)) hk (diag G.obj.X.left))
    (hft : HoldsOnEveryEtaleChart B (Spec (CommRingCat.of k)) hk
      (@_root_.AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      G.obj.X.hom)
    (h0AEMfibres : ∀ n : ℕ, 0 < n →
      ∀ Z : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u,
        IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk Z →
        ∀ z : Z ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk))),
          IsSeparated B (Spec (CommRingCat.of k)) hk z →
          IsFiniteType B (Spec (CommRingCat.of k)) hk z →
          ∀ w : (∏ᶜ fun _ : Fin n => (Over.post B.inclusion).op ⋙ yoneda.obj (Over.mk
              (projectiveSpaceOverRing 1 (CommRingCat.of k) ↘
                Spec (CommRingCat.of k)))) ⟶ Z,
            ∃ (I : Finset (Fin n))
              (g : (∏ᶜ fun _ : I => (Over.post B.inclusion).op ⋙ yoneda.obj (Over.mk
                (projectiveSpaceOverRing 1 (CommRingCat.of k) ↘
                  Spec (CommRingCat.of k)))) ⟶ Z),
              w = Pi.map' (fun i : I => (i : Fin n)) (fun _ => 𝟙 _) ≫ g ∧
                ∀ y : points B (Spec (CommRingCat.of k)) hk Z,
                  {x : points B (Spec (CommRingCat.of k)) hk
                      (∏ᶜ fun _ : I => (Over.post B.inclusion).op ⋙ yoneda.obj (Over.mk
                        (projectiveSpaceOverRing 1 (CommRingCat.of k) ↘
                          Spec (CommRingCat.of k)))) |
                    pointsMap B (Spec (CommRingCat.of k)) hk
                      (∏ᶜ fun _ : I => (Over.post B.inclusion).op ⋙ yoneda.obj (Over.mk
                        (projectiveSpaceOverRing 1 (CommRingCat.of k) ↘
                          Spec (CommRingCat.of k)))) g x = y}.Finite)
    (f : Over.mk
        (((Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 (B.obj hk)))).isTerminalObj yoneda
            (Over.mk (𝟙 (B.obj hk)))).from
          (∏ᶜ fun _ : Fin 1 => (Over.post B.inclusion).op ⋙ yoneda.obj (Over.mk
            (projectiveSpaceOverRing 1 (CommRingCat.of k) ↘ Spec (CommRingCat.of k))))) ⟶
      G.obj.X) :
    ∃ c : yoneda.obj (Over.mk (𝟙 (B.obj hk))) ⟶ G.obj.X.left,
      c ≫ G.obj.X.hom = 𝟙 (yoneda.obj (Over.mk (𝟙 (B.obj hk)))) ∧
        f.left =
          (((Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 (B.obj hk)))).isTerminalObj yoneda
              (Over.mk (𝟙 (B.obj hk)))).from
            (∏ᶜ fun _ : Fin 1 => (Over.post B.inclusion).op ⋙ yoneda.obj (Over.mk
              (projectiveSpaceOverRing 1 (CommRingCat.of k) ↘
                Spec (CommRingCat.of k))))) ≫ c :=
  morphism_projectiveLine_eq_constant k B hk G hsep hft h0AEMfibres f

/-! ### Factoring a morphism out of a finite power of the projective line -/

section Factorization

attribute [local instance] pointTopology

/-- The projection of a finite power of the projective line onto the coordinates in *all* of
`Fin n`, as an isomorphism: it is `CategoryTheory.Limits.Pi.map'` along the bijection between
`Finset.univ` and `Fin n`, with inverse the reindexing along the opposite bijection. -/
noncomputable def coordinateProjectionUnivIso (n : ℕ) :
    projectiveLinePower k B hk (Fin n) ≅
      projectiveLinePower k B hk (Finset.univ : Finset (Fin n)) where
  hom := coordinateProjection k B hk n Finset.univ
  inv := Pi.map' (fun i : Fin n => (⟨i, Finset.mem_univ i⟩ :
      (Finset.univ : Finset (Fin n)))) fun _ => 𝟙 (projectiveLineFunctor k B hk)
  hom_inv_id := by
    apply Pi.hom_ext
    intro i
    simp
  inv_hom_id := by
    apply Pi.hom_ext
    intro j
    simp

/-- The case `m = n` of Stacks 0AEM. Let `k` be a field, let `n` be a positive integer and
let `w : (ℙ¹_k)^n ⟶ Z` be a morphism to an algebraic space `Z` which is separated and of finite
type over `k`. If every fibre of `w` on points is finite, then `w` factors as the projection
onto all `n` coordinates followed by a finite morphism; equivalently, `w` is itself finite.

Such a `w` is finite by
`AlgebraicGeometry.Space.isFinite_of_finite_fibres`, and the projection onto all `n`
coordinates is an isomorphism, so the required factorization is given by its inverse followed
by `w`, which is finite because an isomorphism is a closed immersion and therefore finite.

This is a component carrying no tag; Stacks 0AEM itself is
`AlgebraicGeometry.Space.exists_coordinateProjection_isFinite`. -/
theorem exists_coordinateProjection_isFinite_of_finite_fibres (n : ℕ) (_hn : 0 < n)
    (Z : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u)
    (hZ : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk Z)
    (z : Z ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk))))
    (hsep : IsSeparated B (Spec (CommRingCat.of k)) hk z)
    (_hft : IsFiniteType B (Spec (CommRingCat.of k)) hk z)
    (w : projectiveLinePower k B hk (Fin n) ⟶ Z)
    (hfib : ∀ y : points B (Spec (CommRingCat.of k)) hk Z,
      {x : points B (Spec (CommRingCat.of k)) hk (projectiveLinePower k B hk (Fin n)) |
        pointsMap B (Spec (CommRingCat.of k)) hk (projectiveLinePower k B hk (Fin n)) w x =
          y}.Finite) :
    ∃ (I : Finset (Fin n)) (g : projectiveLinePower k B hk I ⟶ Z),
      w = coordinateProjection k B hk n I ≫ g ∧
        IsFinite B (Spec (CommRingCat.of k)) hk g := by
  classical
  -- the projection onto all `n` coordinates is an isomorphism
  let eu := coordinateProjectionUnivIso k B hk n
  refine ⟨Finset.univ, eu.inv ≫ w, (eu.hom_inv_id_assoc w).symm, ?_⟩
  exact isFinite_iso_hom_comp k B hk eu.symm
    (isFinite_of_finite_fibres k B hk (Fin n) Z hZ z hsep w hfib)

/-- Stacks 0AEM with its contraction step assumed. Let `k` be a field, let `n` be a
positive integer and let `w : (ℙ¹_k)^n ⟶ Z` be a morphism to an algebraic space `Z` which is
separated and of finite type over `k`. If `w` factors as the projection onto the coordinates in
some finite subset `I ⊆ Fin n` followed by a morphism whose fibres on points are all finite,
then it factors as that projection followed by a *finite* morphism.

The hypothesis is the state the source reaches after its contraction process — the step which
is not in this file — and the conclusion is the statement of 0AEM: the second morphism is
finite by `AlgebraicGeometry.Space.isFinite_of_finite_fibres`, there applied to the power of
the projective line indexed by `I`.

This is a component carrying no tag; Stacks 0AEM itself, with the contraction step discharged,
is `AlgebraicGeometry.Space.exists_coordinateProjection_isFinite`. -/
theorem exists_coordinateProjection_isFinite_of_exists_finite_fibres
    (n : ℕ) (_hn : 0 < n)
    (Z : (BigFppfOver B (Spec (CommRingCat.of k)) hk)ᵒᵖ ⥤ Type u)
    (hZ : IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk Z)
    (z : Z ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk))))
    (hsep : IsSeparated B (Spec (CommRingCat.of k)) hk z)
    (_hft : IsFiniteType B (Spec (CommRingCat.of k)) hk z)
    (w : projectiveLinePower k B hk (Fin n) ⟶ Z)
    (hcontraction : ∃ (I : Finset (Fin n)) (g : projectiveLinePower k B hk I ⟶ Z),
      w = coordinateProjection k B hk n I ≫ g ∧
        ∀ y : points B (Spec (CommRingCat.of k)) hk Z,
          {x : points B (Spec (CommRingCat.of k)) hk (projectiveLinePower k B hk I) |
            pointsMap B (Spec (CommRingCat.of k)) hk (projectiveLinePower k B hk I) g x =
              y}.Finite) :
    ∃ (I : Finset (Fin n)) (g : projectiveLinePower k B hk I ⟶ Z),
      w = coordinateProjection k B hk n I ≫ g ∧
        IsFinite B (Spec (CommRingCat.of k)) hk g := by
  obtain ⟨I, g, hfac, hfib⟩ := hcontraction
  exact ⟨I, g, hfac, isFinite_of_finite_fibres k B hk I Z hZ z hsep g hfib⟩

end Factorization

end AlgebraicGeometry.Space

end
