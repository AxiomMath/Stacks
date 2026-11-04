module

public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineFibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TensorLiftSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent

/-!
# Separation axioms for a formal algebraic space

Let `S` be a scheme contained in a big fppf site `B` and let `X` be a formal algebraic space
over `S`. **Stacks 0AJ7** names two separation axioms for `X`: it is *quasi-separated* when the
equivalent conditions of Stacks 0AJ5 hold, and *separated* when the equivalent conditions of
Stacks 0AJ6 hold.

Separatedness in the form of clause (2) of Stacks 0AJ6 is
`AlgebraicGeometry.FormalSpace.IsSeparated`. This file defines quasi-separatedness in the form
of clause (3) of Stacks 0AJ5 — the fibre product of two affine scheme-valued points of `X` is
quasi-compact — proves that separated implies quasi-separated, and proves both axioms for an
affine formal algebraic space.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsQuasiSeparated`: quasi-separatedness of an fppf sheaf, in
  the form of clause (3) of **Stacks 0AJ5**.

## Main results

* `AlgebraicGeometry.FormalSpace.isQuasiSeparated_of_isSeparated`: a separated fppf sheaf is
  quasi-separated.
* `AlgebraicGeometry.FormalSpace.IsAffineFormalAlgebraicSpace.isSeparated` and
  `AlgebraicGeometry.FormalSpace.isQuasiSeparated_of_isAffineFormalAlgebraicSpace`:
  **Stacks 0AJ7**, an affine formal algebraic space is separated and quasi-separated.
* `AlgebraicGeometry.FormalSpace.isSeparatedMorphism_of_isClosedImmersion_diag`:
  **Stacks 0APX**, a morphism from a separated algebraic space over `S` to a formal algebraic
  space over `S` is separated.
* `AlgebraicGeometry.FormalSpace.isSeparatedMorphism_pullbackSnd_of_isClosedImmersion_diag`:
  the base change of such a morphism along any morphism to its target is separated.

## Implementation notes

Both axioms are stated for an arbitrary fppf sheaf rather than as a separation property of the
reduction of a formal algebraic space. Quasi-separatedness is taken in clause (3) of
Stacks 0AJ5, with affine `U` and `V`. As for separatedness, the fibre product is presented by a
cartesian square over the sheafified Yoneda embedding together with an object of the site
representing it, and quasi-compactness of that object is `CompactSpace` on its underlying
scheme. Both conditions quantify over the representing objects, so they hold vacuously on a
sheaf whose fibre products are not representable.

Separatedness of a sheaf `U` over `S` is the closed immersion condition on the diagonal
`U ⟶ U ⨯ U`, which is **Stacks 02X5** for the separatedness axiom: the product is taken in the
fppf sheaves over `S`, hence is the fibre product over `S`, and closed immersions are those of
`AlgebraicGeometry.FormalSpace.IsClosedImmersion`.

## References

* [Stacks Project, Tag 02X5](https://stacks.math.columbia.edu/tag/02X5)
* [Stacks Project, Tag 04ZI](https://stacks.math.columbia.edu/tag/04ZI)
* [Stacks Project, Tag 0AI8](https://stacks.math.columbia.edu/tag/0AI8)
* [Stacks Project, Tag 0AJ5](https://stacks.math.columbia.edu/tag/0AJ5)
* [Stacks Project, Tag 0AJ6](https://stacks.math.columbia.edu/tag/0AJ6)
* [Stacks Project, Tag 0AJ7](https://stacks.math.columbia.edu/tag/0AJ7)
* [Stacks Project, Tag 0APX](https://stacks.math.columbia.edu/tag/0APX)
* [Stacks Project, Tag 0ARN](https://stacks.math.columbia.edu/tag/0ARN)
* [Stacks Project, Tag 0ARS](https://stacks.math.columbia.edu/tag/0ARS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Quasi-separatedness -/

/-- An fppf sheaf `X` on the big fppf site of `S` is *quasi-separated* when, for every pair of
morphisms to `X` from sheaves represented by affine schemes over `S`, every object of the site
representing their fibre product has quasi-compact underlying scheme. -/
@[stacks 0AJ7 "clause (1): quasi-separated, in the form of clause (3) of Stacks 0AJ5, whose \
equivalence with clause (2) of Stacks 0AJ5 and with quasi-separatedness of the reduction is \
not proved in this library"]
abbrev IsQuasiSeparated (X : FppfSheaf B S hS) : Prop :=
  ∀ (U V P : BigFppfOver B S hS)
      (f : (fppfYoneda B S hS).obj U ⟶ X) (g : (fppfYoneda B S hS).obj V ⟶ X)
      (p : P ⟶ U) (q : P ⟶ V),
    IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
    IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
    IsPullback ((fppfYoneda B S hS).map p) ((fppfYoneda B S hS).map q) f g →
    CompactSpace ((BigFppfOver.toScheme B S hS).obj P)

/-- A separated fppf sheaf on the big fppf site of `S` is quasi-separated. -/
theorem isQuasiSeparated_of_isSeparated {X : FppfSheaf B S hS} (hX : IsSeparated B S hS X) :
    IsQuasiSeparated B S hS X := fun U V P f g p q hU hV sq ↦
  have _ := (hX U V P f g p q hU hV sq).1
  inferInstance

/-! ### Separatedness of an affine formal algebraic space -/

/-- Every affine formal algebraic space over `S` is separated, in the form of clause (2) of
Stacks 0AJ6. -/
@[stacks 0AJ7 "clause (2): an affine formal algebraic space is separated, in the form of \
clause (2) of Stacks 0AJ6, whose equivalence with clause (1) is not proved in this library"]
theorem IsAffineFormalAlgebraicSpace.isSeparated {X : FppfSheaf B S hS}
    (hX : IsAffineFormalAlgebraicSpace B S hS X) : IsSeparated B S hS X := by
  intro U V P a b p q hU hV sq
  let T := BigFppfOver.toScheme B S hS
  let F := fppfYoneda B S hS
  let _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let _ : F.Full := (Sheaf.fullyFaithfulSheafifiedYoneda (BigFppfOver.topology B S hS)).full
  let _ : F.Faithful :=
    (Sheaf.fullyFaithfulSheafifiedYoneda (BigFppfOver.topology B S hS)).faithful
  let _ : PreservesLimitsOfShape WalkingCospan F := by
    dsimp only [F, fppfYoneda, Sheaf.sheafifiedYoneda]
    infer_instance
  let _ := hU
  let _ := hV
  obtain ⟨T₁, g₁, h₁, hr₁, ht₁, he₁⟩ :=
    ((isAffineFormalAlgebraicSpace_iff B S hS X).mp hX).1 ⟨U, hU⟩ a
  have hthick : Stacks.Thickenings.IsThickening (T.map (hr₁.snd b)) :=
    ht₁.property b (hr₁.fst b) (hr₁.snd b) (hr₁.isPullback b)
  have _ := hthick.1
  obtain ⟨hQaff, hQsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine
    (T.map (hr₁.snd b))
  have _ := hQaff
  have _ : IsAffine (T.obj ((BigAffineFppf.inclusion B S hS).obj T₁)) := T₁.property
  let m : U ⟶ (BigAffineFppf.inclusion B S hS).obj T₁ := F.preimage g₁
  let n : hr₁.pullback b ⟶ (BigAffineFppf.inclusion B S hS).obj T₁ := hr₁.fst' b
  have sqTot : IsPullback (F.map (pullback.fst m n))
      (F.map (pullback.snd m n ≫ hr₁.snd b)) a b := by
    have h1 : IsPullback (F.map (pullback.fst m n)) (F.map (pullback.snd m n)) g₁
        (hr₁.fst b) := by
      have h0 := (IsPullback.of_hasPullback m n).map F
      rwa [show F.map m = g₁ from F.map_preimage g₁,
        show F.map n = hr₁.fst b from hr₁.map_fst' b] at h0
    have h2 := h1.paste_vert (hr₁.isPullback b)
    rw [F.map_comp]
    rwa [he₁] at h2
  obtain ⟨e, hefst, hesnd⟩ : ∃ e : P ≅ pullback m n,
      e.hom ≫ pullback.fst m n = p ∧ e.hom ≫ pullback.snd m n ≫ hr₁.snd b = q := by
    refine ⟨F.preimageIso (sq.isoIsPullback _ _ sqTot), F.map_injective ?_, F.map_injective ?_⟩
    all_goals rw [F.map_comp, Functor.preimageIso_hom, F.map_preimage]
    · exact sq.isoIsPullback_hom_fst _ _ sqTot
    · exact sq.isoIsPullback_hom_snd _ _ sqTot
  have sqSch : IsPullback (T.map (pullback.fst m n)) (T.map (pullback.snd m n)) (T.map m)
      (T.map n) := (IsPullback.of_hasPullback m n).map T
  have _ : IsAffine (T.obj (pullback m n)) := IsAffine.of_isPullback sqSch
  have hsurjR : Function.Surjective (Algebra.TensorProduct.lift
      (T.map (pullback.fst m n)).appTop.hom.toIntAlgHom
      (T.map (pullback.snd m n) ≫ T.map (hr₁.snd b)).appTop.hom.toIntAlgHom
      (fun _ _ ↦ Commute.all _ _)) :=
    tensor_lift_surjective_of_isPullback_comp sqSch _ hQsurj
  have hiso : Function.Surjective (T.map e.hom).appTop.hom :=
    (ConcreteCategory.bijective_of_isIso ((T.map e.hom).app ⊤)).2
  refine ⟨IsAffine.of_isIso (T.mapIso e).hom, ?_⟩
  refine tensor_lift_surjective_congr
    (p := T.map e.hom ≫ T.map (pullback.fst m n))
    (q := T.map e.hom ≫ T.map (pullback.snd m n) ≫ T.map (hr₁.snd b))
    (by rw [← T.map_comp, hefst]) (by rw [← T.map_comp, ← T.map_comp, hesnd]) ?_
  exact tensor_lift_surjective_comp _ _ _ hiso hsurjR

/-- An affine formal algebraic space over `S` admitting a morphism to a sheaf represented by an
affine scheme of the site is separated. -/
theorem isSeparated_of_isAffineFormalAlgebraicSpace {X : FppfSheaf B S hS}
    {Z : BigFppfOver B S hS} (_hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj Z))
    (_f : X ⟶ (fppfYoneda B S hS).obj Z) (hX : IsAffineFormalAlgebraicSpace B S hS X) :
    IsSeparated B S hS X :=
  IsAffineFormalAlgebraicSpace.isSeparated (X := X) (hX := hX)

/-- The sheaf represented by the terminal object of the big fppf site of `S` is terminal. -/
noncomputable def fppfYonedaTerminalIsTerminal :
    IsTerminal ((fppfYoneda B S hS).obj (⊤_ (BigFppfOver B S hS))) := by
  let J := BigFppfOver.topology B S hS
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let eH : J.uliftYoneda.{u + 1} ≅ Sheaf.sheafifiedYoneda J :=
    Functor.isoWhiskerLeft J.uliftYoneda
        (sheafificationNatIso.{u, u + 1, u + 1, u + 2} J (Type (u + 1))) ≪≫
      Functor.isoWhiskerRight J.uliftYonedaCompSheafToPresheaf
        (presheafToSheaf J (Type (u + 1)))
  let _ : PreservesLimit (Functor.empty (BigFppfOver B S hS)) (Sheaf.sheafifiedYoneda J) :=
    preservesLimit_of_natIso (Functor.empty _) eH
  exact (terminalIsTerminal : IsTerminal (⊤_ (BigFppfOver B S hS))).isTerminalObj
    (Sheaf.sheafifiedYoneda J)

/-- The terminal object of the big fppf site of `S` has affine underlying scheme when `S` is
affine. -/
theorem isAffine_toScheme_terminal (hSaff : IsAffine S) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (⊤_ (BigFppfOver B S hS))) :=
  have e : (BigFppfOver.toScheme B S hS).obj (⊤_ (BigFppfOver B S hS)) ≅ S :=
    (BigFppfOver.toScheme B S hS).mapIso
      (terminalIsTerminal.uniqueUpToIso (Over.mkIdTerminal (X := B.obj hS)))
  have _ := hSaff
  IsAffine.of_isIso e.hom

/-- Over an affine base every affine formal algebraic space is separated. -/
theorem isSeparated_of_isAffineFormalAlgebraicSpace_of_isAffineBase {X : FppfSheaf B S hS}
    (_hSaff : IsAffine S) (hX : IsAffineFormalAlgebraicSpace B S hS X) :
    IsSeparated B S hS X :=
  IsAffineFormalAlgebraicSpace.isSeparated B S hS hX

/-- Every affine formal algebraic space over `S` is quasi-separated, in the form of clause (3)
of Stacks 0AJ5. -/
@[stacks 0AJ7 "clause (1): an affine formal algebraic space is quasi-separated, in the form of \
clause (3) of Stacks 0AJ5"]
theorem isQuasiSeparated_of_isAffineFormalAlgebraicSpace {X : FppfSheaf B S hS}
    (hX : IsAffineFormalAlgebraicSpace B S hS X) :
    IsQuasiSeparated B S hS X :=
  isQuasiSeparated_of_isSeparated B S hS
    (IsAffineFormalAlgebraicSpace.isSeparated B S hS hX)

/-- Over an affine base every affine formal algebraic space is quasi-separated. -/
theorem isQuasiSeparated_of_isAffineFormalAlgebraicSpace_of_isAffineBase
    {X : FppfSheaf B S hS} (_hSaff : IsAffine S)
    (hX : IsAffineFormalAlgebraicSpace B S hS X) :
    IsQuasiSeparated B S hS X :=
  isQuasiSeparated_of_isAffineFormalAlgebraicSpace B S hS hX

/-! ### Morphisms out of a separated algebraic space -/

/-- A morphism `f : U ⟶ X` of fppf sheaves over `S` whose source is separated over `S`, that is
whose diagonal `U ⟶ U ⨯ U` is a closed immersion, is separated. -/
@[stacks 0APX]
theorem isSeparatedMorphism_of_isClosedImmersion_diag {U X : FppfSheaf B S hS}
    (hU : IsClosedImmersion B S hS (diag U)) (f : U ⟶ X) :
    IsSeparatedMorphism B S hS f :=
  isClosedImmersion_of_isPullback B S hS (pullback.isPullback_diagonal_diag f) hU

/-- A morphism out of a sheaf separated over `S` stays separated after a base change: for
`ξ : T ⟶ X` the projection `U ×_X T ⟶ T` is a separated morphism. -/
theorem isSeparatedMorphism_pullbackSnd_of_isClosedImmersion_diag {U X T : FppfSheaf B S hS}
    (hU : IsClosedImmersion B S hS (diag U)) (f : U ⟶ X) (ξ : T ⟶ X) :
    IsSeparatedMorphism B S hS (pullback.snd f ξ) :=
  isSeparatedMorphism_of_isPullback B S hS (IsPullback.of_hasPullback f ξ)
    (isSeparatedMorphism_of_isClosedImmersion_diag B S hS hU f)

end AlgebraicGeometry.FormalSpace

end
