module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.Comap
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.FiberSequence
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.Immersions
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.RegularSliceThroughPoint

/-!
# Slicing by prescribed global sections

Stacks tag 06LI produces its own sections: from elements `h₁, …, h_r` of the local ring
`𝒪_{X, x}` it manufactures an affine open `U₀ ∋ x` and sections `b₁, …, b_r ∈ Γ(U₀, 𝒪_{U₀})`
with germs the `h_i`, and asserts among other things that the zero scheme `V(b)` is flat over
the base.  This file treats the converse reading: the sections `a₁, …, a_r` are *given* as global
functions on `X`, and we find a neighbourhood of `x` on which the zero scheme of **those**
functions is flat over the base.

Applying tag 06LI to the germs of the `a_i` gives sections `b_i` with the same germs at `x`; two
sections with the same germ agree on a neighbourhood, and on such a neighbourhood the two zero
schemes coincide, so the flatness tag 06LI proves for `V(b)` is flatness of `V(a)` there.

## Main results

* `Stacks.AlgebraicGeometry.exists_opens_appTop_eq_of_germ_eq`: finitely many pairs of global
  sections with equal germs at a point have equal restrictions to one open subscheme containing
  it.
* `Stacks.AlgebraicGeometry.exists_affineOpen_flat_ofIdealTop_of_isRegular_fiber`: **the
  converse reading of Stacks tag 06LI.**  For global sections `a₁, …, a_r` of `X` whose germs at
  `x` are a regular sequence on the fibre through `x`, there is an affine open `U ∋ x` on which
  the zero scheme of the restricted sections is flat and locally of finite presentation over the
  base.
* `Stacks.AlgebraicGeometry.exists_affineOpen_flat_ofIdealTop_of_isRegular_fiber_germ`: the same
  with the regularity hypothesis read at a prescribed point of the fibre, in terms of the germs
  of the restrictions of the `a_i` to it.

## Implementation notes

The agreement of the two families of sections is obtained one index at a time from
`TopCat.Presheaf.germ_eq`, and the neighbourhoods are intersected by recursion on `r`, the
restriction of an agreement to a smaller open being
`Stacks.AlgebraicGeometry.restrict_le_eq`.  The agreement is recorded as an equality of
restrictions along `U ≤ ⊤` rather than along `U.ι`, because that form is the one stable under
shrinking; `Stacks.AlgebraicGeometry.appTop_ι_eq_of_restrict_eq` converts it at the end, which
is one more application of the same restriction lemma, because `U.ι.appTop` is by definition the
restriction along `U.ι ''ᵁ ⊤ ≤ ⊤` and `U.ι ''ᵁ ⊤ = U`.

The open produced is affine: the neighbourhood found inside the affine open of tag 06LI is shrunk
to an affine open of `X` inside its image, exactly as in
`Stacks.AlgebraicGeometry.exists_affineOpen_regularImmersion_of_isRegular_fiber`, and the
comparison morphism back to that neighbourhood is `AlgebraicGeometry.IsOpenImmersion.lift`.
Flatness travels along the inclusion by `Stacks.AlgebraicGeometry.flat_comap_of_isOpenImmersion`
and the ideal sheaf by `Stacks.AlgebraicGeometry.comap_ofIdealTop`, whose affineness hypothesis is
met by the open of tag 06LI; no affineness of `X` is assumed or used.

## References

* [Stacks Project, Lemma 37.24.1 (Tag 06LI)](https://stacks.math.columbia.edu/tag/06LI)
* [Stacks Project, Lemma 76.28.1 (Tag 06LW)](https://stacks.math.columbia.edu/tag/06LW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

namespace Stacks.AlgebraicGeometry

universe u

variable {Z : Scheme.{u}}

/-- Restricting an agreement of two global sections to a smaller open. -/
theorem restrict_le_eq {O O' : Z.Opens} (h : O' ≤ O) {s t : Γ(Z, ⊤)}
    (hst : Z.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op s =
      Z.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op t) :
    Z.presheaf.map (homOfLE (le_top : O' ≤ ⊤)).op s =
      Z.presheaf.map (homOfLE (le_top : O' ≤ ⊤)).op t := by
  have key : ∀ c : Γ(Z, ⊤), Z.presheaf.map (homOfLE (le_top : O' ≤ ⊤)).op c =
      Z.presheaf.map (homOfLE h).op (Z.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op c) := by
    intro c
    rw [← CommRingCat.comp_apply, ← Z.presheaf.map_comp]
    rfl
  rw [key, key, hst]

/-- The restriction of a global section along `O.ι` is its restriction along `O ≤ ⊤`, so an
agreement in the latter form is an agreement in the former. -/
theorem appTop_ι_eq_of_restrict_eq (O : Z.Opens) {s t : Γ(Z, ⊤)}
    (h : Z.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op s =
      Z.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op t) :
    O.ι.appTop s = O.ι.appTop t := by
  rw [Scheme.Opens.ι_appTop]
  exact restrict_le_eq (le_of_eq (Scheme.Opens.ι_image_top O)) h

/-- Finitely many pairs of global sections with equal germs at a point agree on a single open
neighbourhood of that point: each pair agrees on one, and the finitely many neighbourhoods are
intersected. -/
theorem exists_opens_restrict_eq_of_germ_eq (z : Z) :
    ∀ (r : ℕ) (s t : Fin r → Γ(Z, ⊤)),
      (∀ i, Z.presheaf.germ ⊤ z trivial (s i) = Z.presheaf.germ ⊤ z trivial (t i)) →
      ∃ O : Z.Opens, z ∈ O ∧ ∀ i,
        Z.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (s i) =
          Z.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (t i) := by
  intro r
  induction r with
  | zero => exact fun _ _ _ => ⟨⊤, trivial, fun i => i.elim0⟩
  | succ n ih =>
    intro s t h
    obtain ⟨O, hzO, hO⟩ := ih (fun i => s i.succ) (fun i => t i.succ) fun i => h i.succ
    obtain ⟨W, hzW, iU, iV, hW⟩ :=
      Z.presheaf.germ_eq (U := ⊤) (V := ⊤) z trivial trivial (s 0) (t 0) (h 0)
    have hW' : Z.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (s 0) =
        Z.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (t 0) := hW
    refine ⟨O ⊓ W, ⟨hzO, hzW⟩, fun i => ?_⟩
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · exact restrict_le_eq inf_le_right hW'
    · exact restrict_le_eq inf_le_left (hO j)

/-- Finitely many pairs of global sections with equal germs at a point have equal restrictions
to one open subscheme containing it. -/
theorem exists_opens_appTop_eq_of_germ_eq (z : Z) {r : ℕ} (s t : Fin r → Γ(Z, ⊤))
    (h : ∀ i, Z.presheaf.germ ⊤ z trivial (s i) = Z.presheaf.germ ⊤ z trivial (t i)) :
    ∃ O : Z.Opens, z ∈ O ∧ ∀ i, O.ι.appTop (s i) = O.ι.appTop (t i) := by
  obtain ⟨O, hzO, hO⟩ := exists_opens_restrict_eq_of_germ_eq z r s t h
  exact ⟨O, hzO, fun i => appTop_ι_eq_of_restrict_eq O (hO i)⟩

/-- **Stacks tag 06LI read for prescribed global sections.**  Let `f : X ⟶ S` be locally of
finite presentation and flat at `x : X`, and let `a₁, …, a_r ∈ Γ(X, 𝒪_X)` be global sections
whose germs at `x` map to a regular sequence in the local ring of the fibre `X_{f x}` at `x`.
Then there is an affine open `U ⊆ X` containing `x` such that the zero scheme of the
restrictions `a_i|_U` is flat and locally of finite presentation over `S`.

Tag 06LI itself produces sections `b₁, …, b_r` of an affine open `U₀ ∋ x` with prescribed germs
and asserts flatness of `V(b)`; here the germs prescribed are those of the `a_i`, so `a_i|_{U₀}`
and `b_i` have the same germ at `x` and therefore agree on an open neighbourhood of `x` inside
`U₀`.  On an affine open `U` of `X` inside the image of that neighbourhood the two zero schemes
are the same closed subscheme, and flatness of `V(b)` over `S` restricts to it along the open
immersion. -/
theorem exists_affineOpen_flat_ofIdealTop_of_isRegular_fiber {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (x : X) {r : ℕ} (a : Fin r → Γ(X, ⊤))
    (hflat : IsFlatAt f.toLRSHom.toShHom x)
    (hregular : RingTheory.Sequence.IsRegular
      ((f.fiber (f x)).presheaf.stalk (f.asFiber x))
      (List.ofFn fun i : Fin r =>
        ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom
          ((f.fiberι_asFiber x).symm ▸ X.presheaf.germ ⊤ x trivial (a i)))) :
    ∃ (U : X.affineOpens) (_ : x ∈ U.1),
      Flat ((Scheme.IdealSheafData.ofIdealTop
          (Ideal.ofList (List.ofFn fun i => U.1.ι.appTop (a i)))).subschemeι ≫ U.1.ι ≫ f) ∧
        LocallyOfFinitePresentation ((Scheme.IdealSheafData.ofIdealTop
          (Ideal.ofList (List.ofFn fun i => U.1.ι.appTop (a i)))).subschemeι ≫ U.1.ι ≫ f) := by
  classical
  obtain ⟨U₀, hxU₀, b, hgerm, -, -, hflatT, -, -⟩ :=
    exists_affineOpen_regularImmersion_flat_of_isRegular_fiber f x
      (fun i => X.presheaf.germ ⊤ x trivial (a i)) hflat hregular
  have hU₀aff : IsAffine U₀.1.toScheme := U₀.2
  set T := Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn b)) with hT
  have hflatT' : Flat (T.subschemeι ≫ U₀.1.ι ≫ f) := hflatT
  have hgerm' (i : Fin r) : U₀.1.toScheme.presheaf.germ ⊤ (⟨x, hxU₀⟩ : U₀.1.toScheme) trivial
        (U₀.1.ι.appTop (a i)) =
      U₀.1.toScheme.presheaf.germ ⊤ (⟨x, hxU₀⟩ : U₀.1.toScheme) trivial (b i) := by
    refine Eq.trans ?_ (hgerm i)
    refine Eq.trans (congrArg (fun k : Γ(X, ⊤) ⟶
        U₀.1.toScheme.presheaf.stalk (⟨x, hxU₀⟩ : U₀.1.toScheme) => k.hom (a i))
      (appTop_comp_germ_top U₀.1.ι (⟨x, hxU₀⟩ : U₀.1.toScheme))) ?_
    exact congrArg (U₀.1.ι.stalkMap (⟨x, hxU₀⟩ : U₀.1.toScheme)).hom
      (cast_germ_top (show U₀.1.ι (⟨x, hxU₀⟩ : U₀.1.toScheme) = x from rfl).symm (a i)).symm
  obtain ⟨O, hyO, hO⟩ := exists_opens_appTop_eq_of_germ_eq (⟨x, hxU₀⟩ : U₀.1.toScheme)
    (fun i => U₀.1.ι.appTop (a i)) b hgerm'
  have hxW : x ∈ U₀.1.ι ''ᵁ O := ⟨⟨x, hxU₀⟩, hyO, rfl⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxW (U₀.1.ι ''ᵁ O).isOpen
  let Va : X.affineOpens := ⟨V, hV⟩
  have hVaff : IsAffine Va.1.toScheme := hV
  have hVU : Va.1 ≤ U₀.1 := fun t ht => by
    obtain ⟨w, -, rfl⟩ := hVW ht
    exact w.property
  let jv := X.homOfLE hVU
  have hjι : jv ≫ U₀.1.ι = Va.1.ι := X.homOfLE_ι hVU
  have hjvO : Set.range jv ⊆ Set.range O.ι := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨w', hw', hw'eq⟩ := hVW w.property
    exact ⟨⟨w', hw'⟩, U₀.1.ι.isOpenEmbedding.injective
      (show w'.val = (jv w).val from hw'eq.trans (X.homOfLE_apply hVU w).symm)⟩
  let kv := IsOpenImmersion.lift O.ι jv hjvO
  have hkO : kv ≫ O.ι = jv := IsOpenImmersion.lift_fac _ _ _
  have happ (i : Fin r) : jv.appTop (b i) = Va.1.ι.appTop (a i) := by
    rw [← hjι, ← hkO]
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hO i]
  have hcomap : T.comap jv =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.ofList (List.ofFn fun i => Va.1.ι.appTop (a i))) := by
    rw [hT, comap_ofIdealTop, Ideal.map_ofList, List.map_ofFn]
    exact congrArg (fun g : Fin r → Γ(Va.1.toScheme, ⊤) =>
      Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn g))) (funext happ)
  have hfl := flat_comap_of_isOpenImmersion T (U₀.1.ι ≫ f) jv
  rw [hcomap] at hfl
  have hlfpI : LocallyOfFinitePresentation (Scheme.IdealSheafData.ofIdealTop
      (Ideal.ofList (List.ofFn fun i => Va.1.ι.appTop (a i)))).subschemeι :=
    locallyOfFinitePresentation_subschemeι_ofIdealTop _ (Submodule.fg_span (List.finite_toSet _))
  exact ⟨Va, hxV, by simpa only [← Category.assoc, hjι] using hfl, inferInstance⟩

/-- **Stacks tag 06LI for prescribed global sections, read at a prescribed point of the
fibre.**  This is
`Stacks.AlgebraicGeometry.exists_affineOpen_flat_ofIdealTop_of_isRegular_fiber` with its
regularity hypothesis stated at a point `y` of the fibre through `x` and in terms of the germs
of the *restrictions* `a_i|_{X_{f x}}`, rather than at
`AlgebraicGeometry.Scheme.Hom.asFiber` and in terms of germs transported along
`AlgebraicGeometry.Scheme.Hom.fiberι_asFiber`.

The two agree: `y` is `f.asFiber x` because `f.fiberι (f x)` is an embedding, hence injective,
and carries both to `x`; and pulling a global section back along `f.fiberι (f x)` commutes with
taking germs, which turns the transported germ into the germ of the restriction. -/
theorem exists_affineOpen_flat_ofIdealTop_of_isRegular_fiber_germ {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (x : X) (y : f.fiber (f x)) (hy : f.fiberι (f x) y = x)
    {r : ℕ} (a : Fin r → Γ(X, ⊤)) (hflat : IsFlatAt f.toLRSHom.toShHom x)
    (hregular : RingTheory.Sequence.IsRegular ((f.fiber (f x)).presheaf.stalk y)
      (List.ofFn fun i : Fin r => (f.fiber (f x)).presheaf.germ ⊤ y trivial
        ((f.fiberι (f x)).appTop (a i)))) :
    ∃ (U : X.affineOpens) (_ : x ∈ U.1),
      Flat ((Scheme.IdealSheafData.ofIdealTop
          (Ideal.ofList (List.ofFn fun i => U.1.ι.appTop (a i)))).subschemeι ≫ U.1.ι ≫ f) ∧
        LocallyOfFinitePresentation ((Scheme.IdealSheafData.ofIdealTop
          (Ideal.ofList (List.ofFn fun i => U.1.ι.appTop (a i)))).subschemeι ≫ U.1.ι ≫ f) := by
  obtain rfl : y = f.asFiber x :=
    (f.fiberι (f x)).isEmbedding.injective (hy.trans (f.fiberι_asFiber x).symm)
  refine exists_affineOpen_flat_ofIdealTop_of_isRegular_fiber f x a hflat ?_
  exact (congrArg List.ofFn (funext fun i => germ_fiberι_appTop_apply f x (a i))) ▸ hregular

end Stacks.AlgebraicGeometry

end
