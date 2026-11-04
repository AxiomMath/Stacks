module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.CycleCoefficientSupport
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ClosedSubschemeFamily
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Restriction
public import StacksFrontier.FieldTheory.InseparableDegreeTensorLength
public import StacksFrontier.RingTheory.Length.Comparison
public import StacksCore.Tactic.StacksAttribute

/-!
# Restriction of the family of cycles associated to a closed subscheme

Let `f : X ⟶ S` be locally of finite type, let `i : Z ⟶ X` be a closed subscheme whose fibres
over `S` satisfy `dim(Z_s) ≤ r`, and let `U ⊆ X` and `V ⊆ S` be open subschemes with
`f(U) ⊆ V`. The scheme-theoretic inverse image `Z ∩ U = Z ×_X U` is a closed subscheme of `U`
whose fibres over `V` are the corresponding open parts of the fibres of `Z`, and the family
`[Z ∩ U / U / V]_r` of Example 0H4S is the restriction to the fibres of `U/V` of the family
`[Z/X/S]_r`.

Coefficientwise this says that an irreducible component of `Z_s` meeting `U_s` has the same
multiplicity there as it has in `Z_s`, that a component not meeting `U_s` contributes nothing,
and that the relative dimension of a point of `U_t` over `κ(t)` equals the relative dimension of
its image in `X_{i t}` over `κ(i t)`.

## Main definitions

* `Stacks.Chow.restrictedFiberClosedSubschemeMap` — the morphism of fibres of the closed
  subschemes induced by the commutative square, which exhibits `(Z ∩ U)_t` as the part of
  `Z_{i t}` lying over `U_t`.

## Main results

* `Stacks.Chow.componentMultiplicity_eq_of_isOpenImmersion` — multiplicity of a component of a
  closed subscheme is unchanged by passing to an open part of it.
* `Stacks.Chow.cycleAssociatedToClosedSubscheme_apply_of_isOpenImmersion` — the coefficients of
  the cycle of a closed subscheme are unchanged by restriction to an open subscheme; this is
  the fibrewise content of the tag.
* `Stacks.Chow.isPullback_restrictedFiberClosedSubschemeMap` — the fibres of `Z ∩ U` over `V`
  are the base changes along `U_t ⟶ X_{i t}` of the fibres of `Z` over `S`.
* `Stacks.Chow.familyAssociatedToClosedSubscheme_openRestriction` — **Tag 0H4T, restriction.**

## Implementation notes

The multiplicity of an irreducible component of a closed subscheme is the length of the local
ring of the subscheme at the component's generic point *over itself*
(`Stacks.Chow.componentMultiplicity_eq_length_stalk`), so it does not refer to the ambient
scheme at all; restriction to an open subscheme therefore changes nothing, and only the
invariance of that length under the isomorphism of local rings induced by an open immersion has
to be proved. The two generic points to be compared need no transport of irreducible
components: the open immersion of subschemes carries one to the other because both have the
same image in the ambient scheme and a closed immersion is injective.

The coefficientwise comparison is carried out for an abstract cartesian square rather than for
the specific fibre products, which is what keeps the pasting isomorphisms of
`Stacks.Chow.restrictedFiberClosedSubschemeMap` out of the proof. The square being cartesian
gives both that the comparison morphism is an open immersion and that the inverse image of the
subscheme in the open part is exactly its intersection with it, through
`AlgebraicGeometry.IsOpenImmersion.range_pullbackFst`.

Both halves of the coefficient comparison need a hypothesis: the generic point of a component
is produced from a point of relative dimension `r` by Tag 02QT, which asks for the
delta-dimension bound on the subscheme. That bound is exactly the source's standing assumption
`dim(Z_s) ≤ r`, carried here as a hypothesis on each fibre as in Example 0H4S; translating it
into the delta-dimension bound on `Z_{i t}` is
`Stacks.Chow.fiberClosedSubscheme_schemeDeltaDimension_le`, and the corresponding bound on the
restricted subscheme `(Z ∩ U)_t` is deduced from that rather than assumed.

The two fibres `U_t` and `X_{i t}` live over the Chow situations of the two different residue
fields `κ(t)` and `κ(i t)`, which the open immersion `i'` identifies; the comparison of
relative dimensions across that identification is
`Stacks.Chow.relativeDimension_eq_of_openImmersion_over_iso`, so no transcendence degree is
computed here.

Only the *restriction* clause of Tag 0H4T is proved here. The other two clauses are proved
elsewhere and in full generality, each by passing to `(Z ⟶ X)_* 𝒪_Z` and invoking the
corresponding clause of Tag 0H4R:
`Stacks.Chow.familyAssociatedToClosedSubscheme_baseChange`, in
`StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ClosedSubschemeBaseChange`, is base change
along an arbitrary morphism of bases, and
`Stacks.Chow.familyAssociatedToClosedSubscheme_flatPullback`, in
`StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ClosedSubschemeFlatPullback`, is flat pullback
along a flat morphism of the source of any relative dimension. The restriction clause is kept
separate because it is proved coefficientwise, which is what the comparison of the two residue
fields `κ(t)` and `κ(i t)` asks for, rather than through the module bridge.

## References

* [Stacks Project, Tag 0H4T](https://stacks.math.columbia.edu/tag/0H4T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Length over itself is a ring-isomorphism invariant -/

/-- Alias of `Module.length_self_eq_of_ringEquiv`. -/
private alias length_self_eq_of_commRingEquiv := Module.length_self_eq_of_ringEquiv

/-! ### Multiplicity of a component under restriction to an open part -/

/-- The multiplicity of an irreducible component of a closed subscheme is unchanged by passing
to an open part of that subscheme: the multiplicity is the length of the local ring of the
subscheme at the component's generic point over itself, and an open immersion induces an
isomorphism of local rings. -/
theorem componentMultiplicity_eq_of_isOpenImmersion {A B W' W : Scheme.{u}} (w' : W' ⟶ A)
    [IsClosedImmersion w'] (w : W ⟶ B) [IsClosedImmersion w] (q : W' ⟶ W) [IsOpenImmersion q]
    (ξ : genericPoints W') (η : genericPoints W) (hη : q ξ.1 = η.1) :
    componentMultiplicity w' ξ = componentMultiplicity w η := by
  rw [componentMultiplicity_eq_length_stalk w' ξ, componentMultiplicity_eq_length_stalk w η,
    ← hη]
  have : IsIso (q.stalkMap ξ.1) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion q)).2 ξ.1
  exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ))
    (length_self_eq_of_commRingEquiv (asIso (q.stalkMap ξ.1)).commRingCatIsoToRingEquiv).symm

/-! ### Cartesian squares over an open immersion -/

section Square

variable {A B W' W : Scheme.{u}} {q : W' ⟶ W} {w' : W' ⟶ A} {w : W ⟶ B} {g : A ⟶ B}

/-- In a cartesian square whose bottom edge is an open immersion, the top edge is an open
immersion, being a base change of it. -/
private theorem isOpenImmersion_fst_of_isPullback [IsOpenImmersion g] (L : IsPullback q w' w g) :
    IsOpenImmersion q := by
  rw [← L.isoPullback_hom_fst]
  infer_instance

/-- In a cartesian square whose bottom edge is an open immersion, the image of the top edge is
the inverse image of the open part. -/
private theorem range_fst_of_isPullback [IsOpenImmersion g] (L : IsPullback q w' w g) :
    Set.range (q : W' → W) = (w : W → B) ⁻¹' Set.range (g : A → B) := by
  have hsurj : Function.Surjective (L.isoPullback.hom : W' → (pullback w g : Scheme.{u})) :=
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso L.isoPullback)).surjective
  have h1 : (q : W' → W) =
      (fun z : (pullback w g : Scheme.{u}) => (pullback.fst w g) z) ∘
        (fun z : W' => (L.isoPullback.hom) z) := by
    funext z
    exact (congrArg (fun m : W' ⟶ W => m z) L.isoPullback_hom_fst).symm
  rw [h1, Set.range_comp, hsurj.range_eq, Set.image_univ,
    AlgebraicGeometry.IsOpenImmersion.range_pullbackFst g w]
  rfl

/-- In a cartesian square whose bottom edge is an open immersion and whose right edge is a
closed immersion, the left edge cuts out exactly the part of the closed subscheme lying in the
open part. -/
private theorem range_snd_eq_preimage_of_isPullback [IsOpenImmersion g] [IsClosedImmersion w]
    (L : IsPullback q w' w g) :
    Set.range (w' : W' → A) = (g : A → B) ⁻¹' Set.range (w : W → B) := by
  have hpt : ∀ z : W', g (w' z) = w (q z) := fun z => by
    simpa only [Scheme.Hom.comp_apply] using (congrArg (fun m : W' ⟶ B => m z) L.w).symm
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨z, rfl⟩
    exact Set.mem_preimage.mpr ⟨q z, (hpt z).symm⟩
  · intro x hx
    obtain ⟨y, hy⟩ := Set.mem_preimage.mp hx
    obtain ⟨z, hz⟩ := (range_fst_of_isPullback L).symm.subset (Set.mem_preimage.mpr ⟨x, hy.symm⟩)
    refine ⟨z, g.isOpenEmbedding.injective ?_⟩
    rw [hpt z, hz, hy]

end Square

/-! ### The coefficients of the cycle of a closed subscheme under open restriction -/

/-- **Chow Homology, Lemma 02RE for an open immersion.** Let `g : A ⟶ B` be an open immersion
of schemes locally of finite type over the bases of two Chow situations identified by `g`, let
`w : W ⟶ B` be a closed subscheme of delta-dimension at most `k`, and let `w' : W' ⟶ A` be its
inverse image, exhibited by a cartesian square over `g`. Then the cycles `[W']_k` and `[W]_k`
have the same coefficient at corresponding points.

Both coefficients vanish where the relative dimension is not `k` and where the point misses the
subscheme; elsewhere both are the multiplicity of the component the point is generic in, and
those multiplicities agree because the comparison morphism of subschemes is an open
immersion. -/
theorem cycleAssociatedToClosedSubscheme_apply_of_isOpenImmersion (Cx Cy : ChowSituation.{u})
    {A B W' W : Scheme.{u}} (sA : A ⟶ Cx.S) [LocallyOfFiniteType sA] (sB : B ⟶ Cy.S)
    [LocallyOfFiniteType sB] (g : A ⟶ B) [IsOpenImmersion g] (w : W ⟶ B) [IsClosedImmersion w]
    (w' : W' ⟶ A) [IsClosedImmersion w'] (q : W' ⟶ W) [IsOpenImmersion q]
    (hsq : q ≫ w = w' ≫ g)
    (hrange : Set.range (w' : W' → A) = (g : A → B) ⁻¹' Set.range (w : W → B)) (k : ℤ)
    (hW : schemeDeltaDimension Cy (w ≫ sB) ≤ (k : EInt))
    (hdim : ∀ x : A, relativeDimension Cx.dimensionFunction sA x =
      relativeDimension Cy.dimensionFunction sB (g x)) (x : A) :
    (cycleAssociatedToClosedSubscheme Cx sA w' k).1 x =
      (cycleAssociatedToClosedSubscheme Cy sB w k).1 (g x) := by
  have hpt : ∀ z : W', g (w' z) = w (q z) := fun z => by
    simpa only [Scheme.Hom.comp_apply] using (congrArg (fun m : W' ⟶ B => m z) hsq).symm
  have hW' : schemeDeltaDimension Cx (w' ≫ sA) ≤ (k : EInt) := by
    refine schemeDeltaDimension_le_of_forall_relativeDimension_le Cx sA w' fun z => ?_
    rw [hdim (w' z), hpt z]
    exact relativeDimension_le_of_schemeDeltaDimension_le Cy sB w hW (q z)
  by_cases hk : relativeDimension Cx.dimensionFunction sA x = k
  · have hkB : relativeDimension Cy.dimensionFunction sB (g x) = k := (hdim x).symm.trans hk
    by_cases hx : x ∈ Set.range (w' : W' → A)
    · have hgx : g x ∈ Set.range (w : W → B) := Set.mem_preimage.mp (hrange.subset hx)
      obtain ⟨ξ, hξ, hcoeff⟩ :=
        cycleAssociatedToClosedSubscheme_apply_eq_componentMultiplicity_of_mem_range
          Cx sA w' k hW' hx hk
      obtain ⟨η, hη, hcoeff'⟩ :=
        cycleAssociatedToClosedSubscheme_apply_eq_componentMultiplicity_of_mem_range
          Cy sB w k hW hgx hkB
      have hqξ : q ξ.1 = η.1 := by
        refine (inferInstance : IsClosedImmersion w).isClosedEmbedding.injective ?_
        rw [← hpt ξ.1, hξ, hη]
      rw [hcoeff, hcoeff', componentMultiplicity_eq_of_isOpenImmersion w' w q ξ η hqξ]
    · have hgx : g x ∉ Set.range (w : W → B) := fun hc =>
        hx (hrange.symm.subset (Set.mem_preimage.mpr hc))
      rw [cycleAssociatedToClosedSubscheme_apply_eq_zero_of_notMem_range Cx sA w' k hx,
        cycleAssociatedToClosedSubscheme_apply_eq_zero_of_notMem_range Cy sB w k hgx]
  · rw [cycleAssociatedToClosedSubscheme_apply_eq_zero_of_relativeDimension_ne Cx sA w' k hk,
      cycleAssociatedToClosedSubscheme_apply_eq_zero_of_relativeDimension_ne Cy sB w k
        fun hc => hk ((hdim x).trans hc)]

/-- **Chow Homology, Lemma 02RE for an open immersion, read off a cartesian square.** The form of
`Stacks.Chow.cycleAssociatedToClosedSubscheme_apply_of_isOpenImmersion` in which the inverse image
`w'` of the closed subscheme `w` is exhibited by a cartesian square over the open immersion `g`. -/
theorem cycleAssociatedToClosedSubscheme_apply_of_isPullback (Cx Cy : ChowSituation.{u})
    {A B W' W : Scheme.{u}} (sA : A ⟶ Cx.S) [LocallyOfFiniteType sA] (sB : B ⟶ Cy.S)
    [LocallyOfFiniteType sB] (g : A ⟶ B) [IsOpenImmersion g] (w : W ⟶ B) [IsClosedImmersion w]
    (w' : W' ⟶ A) [IsClosedImmersion w'] (q : W' ⟶ W) (L : IsPullback q w' w g) (k : ℤ)
    (hW : schemeDeltaDimension Cy (w ≫ sB) ≤ (k : EInt))
    (hdim : ∀ x : A, relativeDimension Cx.dimensionFunction sA x =
      relativeDimension Cy.dimensionFunction sB (g x)) (x : A) :
    (cycleAssociatedToClosedSubscheme Cx sA w' k).1 x =
      (cycleAssociatedToClosedSubscheme Cy sB w k).1 (g x) :=
  have : IsOpenImmersion q := isOpenImmersion_fst_of_isPullback L
  cycleAssociatedToClosedSubscheme_apply_of_isOpenImmersion Cx Cy sA sB g w w' q L.w
    (range_snd_eq_preimage_of_isPullback L) k hW hdim x

variable {X S Z U V : Scheme.{u}}

/-! ### The fibres of the restricted closed subscheme -/

/-- The morphism of fibres of the closed subschemes induced by a commutative square
`j ≫ f = fU ≫ i'` whose vertical maps are open immersions: it carries the fibre
`(Z ∩ U)_t = Z ×_X U_t` to the fibre `Z_{i' t} = Z ×_X X_{i' t}`. -/
def restrictedFiberClosedSubschemeMap (f : X ⟶ S) (fU : U ⟶ V) (j : U ⟶ X) [IsOpenImmersion j]
    (i' : V ⟶ S) (h : j ≫ f = fU ≫ i') (i : Z ⟶ X) [IsClosedImmersion i] (t : V) :
    (pullback (pullback.fst j i) (fU.fiberι t) : Scheme.{u}) ⟶
      (pullback i (f.fiberι (i' t)) : Scheme.{u}) :=
  pullback.lift (pullback.fst (pullback.fst j i) (fU.fiberι t) ≫ pullback.snd j i)
    (pullback.snd (pullback.fst j i) (fU.fiberι t) ≫ restrictedFiberMap f fU j i' h t)
    (by
      rw [Category.assoc, Category.assoc, ← pullback.condition (f := j) (g := i),
        restrictedFiberMap_fiberι f fU j i' h t, ← Category.assoc, ← Category.assoc,
        pullback.condition (f := pullback.fst j i) (g := fU.fiberι t)])

/-- The fibre of `Z ∩ U` over `t` is the base change along `U_t ⟶ X_{i' t}` of the fibre of `Z`
over `i' t`: the square of the two closed subschemes over the open immersion of fibres is
cartesian, by cancelling the cartesian square defining `Z_{i' t}` from the pasted square
exhibiting `Z ×_X U_t` as a fibre product over `X`. -/
theorem isPullback_restrictedFiberClosedSubschemeMap (f : X ⟶ S) (fU : U ⟶ V) (j : U ⟶ X)
    [IsOpenImmersion j] (i' : V ⟶ S) (h : j ≫ f = fU ≫ i') (i : Z ⟶ X) [IsClosedImmersion i]
    (t : V) :
    IsPullback (restrictedFiberClosedSubschemeMap f fU j i' h i t)
      (fiberClosedImmersion fU (pullback.fst j i) t)
      (fiberClosedImmersion f i (i' t))
      (restrictedFiberMap f fU j i' h t) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst i (f.fiberι (i' t))) ?_
    (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback i (f.fiberι (i' t)))
  rw [show restrictedFiberClosedSubschemeMap f fU j i' h i t ≫ pullback.fst i (f.fiberι (i' t)) =
      pullback.fst (pullback.fst j i) (fU.fiberι t) ≫ pullback.snd j i from
    pullback.lift_fst _ _ _,
    restrictedFiberMap_fiberι f fU j i' h t]
  exact (IsPullback.of_hasPullback (pullback.fst j i) (fU.fiberι t)).paste_horiz
    (IsPullback.of_hasPullback j i).flip

/-- The coefficient comparison of two fibre cycles along the open immersion `μ` of fibres induced
by an open restriction `U/V` of `X/S`, when `κ(i' t) ⟶ κ(t)` is an isomorphism and the inverse
image `w'` of the closed subscheme of the fibre is exhibited by a cartesian square. -/
private theorem cycle_apply_fiber_of_isPullback (f : X ⟶ S) [LocallyOfFiniteType f]
    (fU : U ⟶ V) [LocallyOfFiniteType fU] (j : U ⟶ X) (i' : V ⟶ S) (h : j ≫ f = fU ≫ i')
    (t : V) [IsIso (i'.residueFieldMap t)]
    [IsOpenImmersion (restrictedFiberMap f fU j i' h t)] (i : Z ⟶ X) [IsClosedImmersion i]
    {W' : Scheme.{u}} (w' : W' ⟶ fU.fiber t) [IsClosedImmersion w']
    (q : W' ⟶ pullback i (f.fiberι (i' t)))
    (L : IsPullback q w' (fiberClosedImmersion f i (i' t)) (restrictedFiberMap f fU j i' h t))
    (r : ℕ) (hdim : topologicalKrullDim ↥(pullback i (f.fiberι (i' t))) ≤ (r : WithBot ℕ∞))
    (x : fU.fiber t) :
    (cycleAssociatedToClosedSubscheme (fieldChowSituation (V.residueField t))
        (fU.fiberToSpecResidueField t) w' (r : ℤ)).1 x =
      (cycleAssociatedToClosedSubscheme (fieldChowSituation (S.residueField (i' t)))
        (f.fiberToSpecResidueField (i' t)) (fiberClosedImmersion f i (i' t)) (r : ℤ)).1
        (restrictedFiberMap f fU j i' h t x) :=
  cycleAssociatedToClosedSubscheme_apply_of_isPullback _ _ _ _ _ _ w' q L (r : ℤ)
    (schemeDeltaDimension_le_of_forall_relativeDimension_le _ _ _
      (relativeDimension_fiberClosedImmersion_le f i (i' t) hdim))
    (relativeDimension_eq_of_openImmersion_over_iso _ _ _
      (asIso (Spec.map (i'.residueFieldMap t)))
      (restrictedFiberMap_comp_fiberToSpecResidueField f fU j i' h t).symm _ _ (fun _ => by
        rw [fieldChowSituation_dimensionFunction_eq_zero,
          fieldChowSituation_dimensionFunction_eq_zero])) x

/-! ### Tag 0H4T: restriction -/

/-- **The restriction clause of Tag 0H4T over one point of the base.** Let `f : X ⟶ S` be
locally of finite type, let `i : Z ⟶ X` be a closed subscheme, and let `j : U ⟶ X` and
`i' : V ⟶ S` be open subschemes with `fU : U ⟶ V` making the square commute. If the fibre
`Z_{i' t}` has dimension at most `r`, the restriction of `[Z/X/S]_r` to the fibre of `U/V` over
`t` is the member over `t` of `[Z ∩ U / U / V]_r`.

Coefficientwise: restriction preserves the multiplicity of a component of a fibre of `Z` and
the relative dimension of a point of a fibre, and a component of `Z_{i' t}` contributes to the
restricted family exactly when it meets `U_t`. -/
theorem familyAssociatedToClosedSubscheme_openRestriction_apply (f : X ⟶ S)
    [LocallyOfFiniteType f] (fU : U ⟶ V) [LocallyOfFiniteType fU] (j : U ⟶ X) [IsOpenImmersion j]
    (i' : V ⟶ S) [IsOpenImmersion i'] (h : j ≫ f = fU ≫ i') (i : Z ⟶ X) [IsClosedImmersion i]
    (r : ℕ) (t : V)
    (hdim : topologicalKrullDim ↥(pullback i (f.fiberι (i' t))) ≤ (r : WithBot ℕ∞)) :
    (restrictedFamily f fU j i' h r (familyAssociatedToClosedSubscheme f i r)).1 t =
      familyAssociatedToClosedSubscheme fU (pullback.fst j i) r t := by
  apply Subtype.ext
  ext x
  have hIso : IsIso (i'.residueFieldMap t) := by
    have : IsIso (i'.stalkMap t) :=
      (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion i')).2 t
    exact (IsLocalRing.ResidueField.mapEquiv
      (asIso (i'.stalkMap t)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom
  have : IsOpenImmersion (restrictedFiberMap f fU j i' h t) :=
    restrictedFiberMap_isOpenImmersion f fU j i' h t
  refine ((restrictedFamily f fU j i' h r (familyAssociatedToClosedSubscheme f i r)).2 t x).trans ?_
  rw [familyAssociatedToClosedSubscheme_apply, familyAssociatedToClosedSubscheme_apply]
  exact (cycle_apply_fiber_of_isPullback f fU j i' h t i _
    (restrictedFiberClosedSubschemeMap f fU j i' h i t)
    (isPullback_restrictedFiberClosedSubschemeMap f fU j i' h i t) r hdim x).symm

/-- **Stacks Project, Tag 0H4T (restriction).** The construction of Example 0H4S is compatible
with restriction: let `f : X ⟶ S` be locally of finite type, let `i : Z ⟶ X` be a closed
subscheme with `dim(Z_s) ≤ r` for every `s ∈ S`, and let `j : U ⟶ X` and `i' : V ⟶ S` be open
subschemes with `fU : U ⟶ V` making the square commute. Then the restriction of the family
`[Z/X/S]_r` to the fibres of `U/V` is the family `[Z ∩ U / U / V]_r` attached to the closed
subscheme `Z ∩ U = Z ×_X U` of `U`.

Coefficientwise: restriction preserves the multiplicity of a component of a fibre of `Z` and
the relative dimension of a point of a fibre, and a component of `Z_{i' t}` contributes to the
restricted family exactly when it meets `U_t`. The comparison over a single point `t` of `V`
needs the dimension bound only over `i' t`; that is
`Stacks.Chow.familyAssociatedToClosedSubscheme_openRestriction_apply`. -/
@[stacks 0H4T "restriction"]
theorem familyAssociatedToClosedSubscheme_openRestriction (f : X ⟶ S) [LocallyOfFiniteType f]
    (fU : U ⟶ V) [LocallyOfFiniteType fU] (j : U ⟶ X) [IsOpenImmersion j] (i' : V ⟶ S)
    [IsOpenImmersion i'] (h : j ≫ f = fU ≫ i') (i : Z ⟶ X) [IsClosedImmersion i] (r : ℕ)
    (hdim : ∀ s : S,
      topologicalKrullDim ↥(pullback i (f.fiberι s)) ≤ (r : WithBot ℕ∞)) :
    (restrictedFamily f fU j i' h r (familyAssociatedToClosedSubscheme f i r)).1 =
      familyAssociatedToClosedSubscheme fU (pullback.fst j i) r :=
  funext fun t ↦
    familyAssociatedToClosedSubscheme_openRestriction_apply f fU j i' h i r t (hdim (i' t))

/-! ### Base change at a point with trivial residue field extension -/

/-- **The base change clause of Tag 0H4T over one point with trivial residue field extension.**
Let `f : X ⟶ S` be locally of finite type, let `i : Z ⟶ X` be a closed subscheme and let
`g : S' ⟶ S` be a morphism with `κ(g t) ⟶ κ(t)` an isomorphism. If the fibre `Z_{g t}` has
dimension at most `r`, the member over `t` of the family of the inverse image
`Z ×_X (X ×_S S')` has, at a point of the fibre over `t`, the coefficient of `[Z/X/S]_r` at the
corresponding point of the fibre over `g t`.

Only the fibre over `g t` is constrained, which is what distinguishes this from
`Stacks.Chow.familyAssociatedToClosedSubscheme_baseChange`. -/
theorem familyAssociatedToClosedSubscheme_baseChange_apply_of_isIso {S' : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i] (r : ℕ)
    (t : S') [hres : IsIso (g.residueFieldMap t)]
    (hdim : topologicalKrullDim ↥(pullback i (f.fiberι (g t))) ≤ (r : WithBot ℕ∞))
    (x : (pullback.snd f g).fiber t) :
    (familyAssociatedToClosedSubscheme (pullback.snd f g) (pullback.snd i (pullback.fst f g)) r t :
        AlgebraicCycle ((pullback.snd f g).fiber t) ℤ) x =
      (familyAssociatedToClosedSubscheme f i r (g t) : AlgebraicCycle (f.fiber (g t)) ℤ)
        (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t x) := by
  let μ := restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t
  have : IsIso μ := isIso_baseChangeFiberMap f g t
  have hμ : (pullback.snd f g).fiberι t ≫ pullback.fst f g = μ ≫ f.fiberι (g t) :=
    (restrictedFiberMap_fiberι f (pullback.snd f g) (pullback.fst f g) g pullback.condition t).symm
  let q : (pullback (pullback.snd i (pullback.fst f g)) ((pullback.snd f g).fiberι t) :
      Scheme.{u}) ⟶ pullback i (f.fiberι (g t)) :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst i (pullback.fst f g)) (pullback.snd _ _ ≫ μ)
      (by
        rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
          Category.assoc, hμ, Category.assoc])
  have L : IsPullback q
      (fiberClosedImmersion (pullback.snd f g) (pullback.snd i (pullback.fst f g)) t)
      (fiberClosedImmersion f i (g t)) μ := by
    refine IsPullback.of_right (h₁₂ := pullback.fst i (f.fiberι (g t))) ?_
      (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback i (f.fiberι (g t)))
    rw [show q ≫ pullback.fst i (f.fiberι (g t)) =
        pullback.fst _ _ ≫ pullback.fst i (pullback.fst f g) from pullback.lift_fst _ _ _, ← hμ]
    exact (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback i _)
  rw [familyAssociatedToClosedSubscheme_apply, familyAssociatedToClosedSubscheme_apply]
  exact cycle_apply_fiber_of_isPullback f (pullback.snd f g) (pullback.fst f g) g
    pullback.condition t i _ q L r hdim x

end Stacks.Chow

end
