module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralBaseChangeZariskiReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardBaseChange

/-!
# Base change for pushforward of sheaves of sets is Zariski-local on the flat side

Let

```
X <--h-- Y
|f       |e
S <--g-- T
```

be a cartesian square of schemes and let `F` be a sheaf of sets on the small étale site of `T`.
This file reduces invertibility of the canonical base change map `f^{-1}g_*F ⟶ h_*e^{-1}F` to the
case of an affine `X`, by applying the étale-local criterion of Tag 0EZR clause (1) to the
Zariski covering of `X` by its affine opens, each member factoring through `S` itself.

The reduction needs no hypothesis: the intermediate étale `S`-scheme required by Tag 0EZR for a
member `U` of the covering may be taken to be `S` with the identity, which is étale, so the
`i`-th local square is simply the base change of the given square along `U ⟶ X`.

Two base change maps for sheaves of sets on small étale sites are in the library, and the first
result below identifies them. They are the same construction: both are the mate, under the
inverse-image/direct-image adjunctions, of the composite of the two composition isomorphisms of
direct images around the square. The direct image is
`Stacks.EtaleCohomology.smallEtaleDirectImage` in one spelling and the sheaf pushforward along
étale base change in the other, and these are the same functor by `abbrev`; the two adjunctions,
`Stacks.EtaleCohomology.smallEtaleSetsAdjunction` and
`Stacks.EtaleCohomology.smallEtaleInverseImageAdjunction`, are the same term as well. So the
identification is definitional, and with it the locality criterion — which is stated for
`Stacks.EtaleCohomology.smallEtaleSetsBaseChange` — becomes available for the
`Stacks.EtaleCohomology.smallEtaleSetBaseChange` of Tags 0EZX, 0EYS, 0EZZ and 0EZY.

## Main results

* `Stacks.EtaleCohomology.smallEtaleSetBaseChange_eq_smallEtaleSetsBaseChange` — the two
  set-valued base change maps of a commutative square of schemes are equal, together with the
  two transports of invertibility across that equality,
  `Stacks.EtaleCohomology.isIso_smallEtaleSetsBaseChange_of_isIso_smallEtaleSetBaseChange` and
  `Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isIso_smallEtaleSetsBaseChange`.
* `Stacks.EtaleCohomology.affineOpens_mem_etalePrecoverage` — the affine opens of a scheme form
  an étale covering of it.
* `Stacks.EtaleCohomology.affineOpenBaseChangeData` — the data of Tag 0EZR for that covering,
  with the intermediate étale `S`-schemes taken to be `S` itself.
* `Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isAffine_case` — if the base change
  map of every cartesian square over `S` whose upper left corner is affine is an isomorphism,
  then so is the base change map of any cartesian square over `S`.

## Implementation notes

**Why the comparisons of two spellings of the base change map are arranged as they are.** The
locality criterion is applied through
`Stacks.EtaleCohomology.isIso_smallEtaleSetsBaseChange_app_of_isIso_local`, whose statement is
written with the fields of the data. Comparing two spellings of the base change map that differ
in any one argument makes the kernel unfold the map itself, which costs more than the default
budget; that is the cost recorded on
`Stacks.EtaleCohomology.isIso_smallEtaleSetsBaseChange_app_congr_w`, and the same cost occurs
here. Two devices keep every comparison cheap. First, the criterion is reached through a
statement quantified over the data, with the outer square's corners, morphisms, commutativity
proof and sheaf named and identified with the data's fields by `Eq` and `HEq` hypotheses the
caller discharges by `rfl`; substituting those away first leaves the two spellings inside
syntactically equal. It is stated as a `have` inside the proof, the base's own version of it
being private. Second, the assumed affine case is carried in a form whose base is a variable
pinned to `S` by an equation, rather than `S` itself: the local square's base is the data's
field `V i`, and were the hypothesis stated at `S` the two spellings of the base change map
would differ in that corner.

**What the reduction does not do: the affine case itself.** For `S` the spectrum of a separably
closed field that case is reached by the source's proof of Tag 0EZY as follows (Tag 0EZY itself is
proved by a stalkwise argument instead, as
`Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isSepClosed_of_quasiCompact`). An affine
scheme over `Spec k` is a cofiltered limit of affine schemes of finite type over `Spec k`, the
finite-type case being
`Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isSepClosed_locallyOfFiniteType`, and
the passage to the limit is Tag 0EZT clause (1),
`Stacks.EtaleCohomology.LimitSetBaseChange.isIso_smallEtaleSetBaseChange_limit`. That clause is
proved, but it consumes two colimit presentations of Tag 0EYM as hypotheses. One of the two is
free in this application, the base `S` and the sheaf `g_*F` being constant along the system, so
that its colimit diagram is constant; the other,
`h_*e^{-1}F = colim_i r_i^{-1}h_{i, *}e_i^{-1}F`, is Tag 0EYM in degree zero for sheaves of
**sets**, and the library proves Tag 0EYM only for abelian sheaves
(`Stacks.EtaleCohomology.LimitHigherDirectImage.higherDirectImageColimit`, whose coefficient
category is `Ab`). Its degree zero case
(`Stacks.EtaleCohomology.LimitHigherDirectImage.isHigherDirectImageColimit_zero`) is likewise
abelian. That set-valued instance is the one input this route lacks.

Note also that the limit step of Tag 0EZY needs `g` quasi-compact and quasi-separated, the
standing convention of Section 0EZW, which the statement of Tag 0EZY does not repeat. Along the
system only the `X`-corner varies, so the system's lower horizontal morphism is `g` itself at
every level, and Tag 0EZT asks the levels' lower horizontal morphisms to be quasi-compact and
quasi-separated. So the affine case supplied to the reduction below will carry `g`
quasi-compact and quasi-separated, as Section 0EZW does.

It is not possible to avoid the limit argument by widening the covering condition of Tag 0EZX
instead: over a separably closed field that condition asks every étale `X`-scheme to be covered
by quasi-compact connected ones, and for `X = Spec(∏_ℕ k)`, whose space is the Stone-Čech
compactification of `ℕ`, a free ultrafilter has no connected open neighbourhood, while an étale
morphism is open with connected image when its source is connected.

## References

* [Stacks Project, Tag 0EZR](https://stacks.math.columbia.edu/tag/0EZR)
* [Stacks Project, Tag 0EZX](https://stacks.math.columbia.edu/tag/0EZX)
* [Stacks Project, Tag 0EZY](https://stacks.math.columbia.edu/tag/0EZY)
* [Stacks Project, Tag 0EZT](https://stacks.math.columbia.edu/tag/0EZT)
* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology

section Identification

variable {X Y S T : Scheme.{u}}

/-- **The two base change maps for sheaves of sets on small étale sites agree.** For a
commutative square `e ≫ g = h ≫ f` of schemes, `Stacks.EtaleCohomology.smallEtaleSetBaseChange`
and `Stacks.EtaleCohomology.smallEtaleSetsBaseChange` are the same natural transformation
`f^{-1}g_* ⟶ h_*e^{-1}`: each is the mate, under the two inverse-image/direct-image adjunctions
of the small étale sites, of the composite of the two composition isomorphisms of direct images
around the square, and the two spellings of the direct image and of the adjunction are the same
term. -/
theorem smallEtaleSetBaseChange_eq_smallEtaleSetsBaseChange (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S)
    (f : X ⟶ S) (w : e ≫ g = h ≫ f) :
    smallEtaleSetBaseChange.{u, v} e h g f w = smallEtaleSetsBaseChange.{u, v} e h g f w :=
  rfl

/-- Invertibility of the base change map of a commutative square in the spelling of Tag 0EZR
follows from invertibility in the spelling of Tag 0EZX: the two maps are equal. -/
theorem isIso_smallEtaleSetsBaseChange_of_isIso_smallEtaleSetBaseChange (e : Y ⟶ T) (h : Y ⟶ X)
    (g : T ⟶ S) (f : X ⟶ S) (w : e ≫ g = h ≫ f)
    (F : Sheaf T.smallEtaleTopology (Type (max (u + 1) v)))
    (hF : IsIso ((smallEtaleSetBaseChange.{u, v} e h g f w).app F)) :
    IsIso ((smallEtaleSetsBaseChange.{u, v} e h g f w).app F) := by
  rw [← smallEtaleSetBaseChange_eq_smallEtaleSetsBaseChange.{v}]
  exact hF

/-- Invertibility of the base change map of a commutative square in the spelling of Tag 0EZX
follows from invertibility in the spelling of Tag 0EZR: the two maps are equal. -/
theorem isIso_smallEtaleSetBaseChange_of_isIso_smallEtaleSetsBaseChange (e : Y ⟶ T) (h : Y ⟶ X)
    (g : T ⟶ S) (f : X ⟶ S) (w : e ≫ g = h ≫ f)
    (F : Sheaf T.smallEtaleTopology (Type (max (u + 1) v)))
    (hF : IsIso ((smallEtaleSetsBaseChange.{u, v} e h g f w).app F)) :
    IsIso ((smallEtaleSetBaseChange.{u, v} e h g f w).app F) := by
  rw [smallEtaleSetBaseChange_eq_smallEtaleSetsBaseChange.{v}]
  exact hF

end Identification

section AffineLocality

variable {X Y S T : Scheme.{u}}

/-- **The affine opens of a scheme form an étale covering of it.** They are jointly surjective
and open immersions are étale. -/
lemma affineOpens_mem_etalePrecoverage (X : Scheme.{u}) :
    Presieve.ofArrows (fun i : X.affineOpens => ((i : X.Opens)).toScheme)
        (fun i => ((i : X.Opens)).ι) ∈ Scheme.etalePrecoverage X :=
  mem_etalePrecoverage_of_isOpenImmersion _ fun x => by
    obtain ⟨W, hW, hxW, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
    exact ⟨⟨W, hW⟩, by rw [Scheme.Opens.range_ι]; exact hxW⟩

/-- **The data of Tag 0EZR for the covering of `X` by its affine opens.** The covering is the
family of affine opens of `X`, which is jointly surjective and consists of open immersions, hence
is étale; the intermediate étale `S`-scheme of every member is `S` itself with the identity, so
the factorization asked for by Tag 0EZR is the structure morphism `U ⟶ X ⟶ S` itself. The two
fibre products at each index are the chosen pullbacks `U ×_X Y` and `S ×_S T`, and the diagonal
of the local square and its cartesianness are `Stacks.EtaleCohomology.localSquareDiag` and
`Stacks.EtaleCohomology.isPullback_localSquare`. -/
def affineOpenBaseChangeData (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (sq : IsPullback h e f g) (F : Sheaf T.smallEtaleTopology (Type (max (u + 1) v))) :
    EtaleLocalBaseChangeData.{u, u, _, _} (Type (max (u + 1) v)) where
  X := X
  Y := Y
  S := S
  T := T
  f := f
  h := h
  e := e
  g := g
  cartesian := sq
  I := X.affineOpens
  U i := ((i : X.Opens)).toScheme
  u i := ((i : X.Opens)).ι
  cover := affineOpens_mem_etalePrecoverage X
  V _ := S
  v _ := 𝟙 S
  etale_v _ := inferInstance
  f_i i := ((i : X.Opens)).ι ≫ f
  factorization _ := Category.comp_id _
  Y_i i := pullback ((i : X.Opens)).ι h
  h_i _ := pullback.fst _ _
  toY_i _ := pullback.snd _ _
  upper_cartesian _ := IsPullback.of_hasPullback _ _
  T_i _ := pullback (𝟙 S) g
  g_i _ := pullback.fst _ _
  toT_i _ := pullback.snd _ _
  lower_cartesian _ := IsPullback.of_hasPullback _ _
  e_i _ := localSquareDiag sq (Category.comp_id _) (IsPullback.of_hasPullback _ _)
    (IsPullback.of_hasPullback _ _)
  e_i_compatible _ := localSquareDiag_comp_snd _ _ _ _
  local_cartesian _ := isPullback_localSquare _ _ _ _
  F := F

/-- The upper left corner of the `i`-th local square of
`Stacks.EtaleCohomology.affineOpenBaseChangeData` is affine, by choice of the covering. -/
instance isAffine_affineOpenBaseChangeData_U (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (sq : IsPullback h e f g) (F : Sheaf T.smallEtaleTopology (Type (max (u + 1) v)))
    (i : X.affineOpens) :
    IsAffine ((affineOpenBaseChangeData.{v} f h e g sq F).U i) :=
  inferInstanceAs (IsAffine ((i : X.Opens)).toScheme)

/-- **The hypothesis of Tag 0EZR clause (1) for the covering of `X` by its affine opens**, from
the affine case: the `i`-th local square of
`Stacks.EtaleCohomology.affineOpenBaseChangeData` is a cartesian square over `S` whose upper
left corner is affine, so the assumed affine case applies to it. -/
private theorem isIso_smallEtaleSetsBaseChange_affineOpenBaseChangeData_local (f : X ⟶ S)
    (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S) (sq : IsPullback h e f g)
    (F : Sheaf T.smallEtaleTopology (Type (max (u + 1) v)))
    (haff : ∀ (X₀ Y₀ S₀ T₀ : Scheme.{u}) (f₀ : X₀ ⟶ S₀) (h₀ : Y₀ ⟶ X₀) (e₀ : Y₀ ⟶ T₀)
      (g₀ : T₀ ⟶ S₀) (sq₀ : IsPullback h₀ e₀ f₀ g₀), S₀ = S → IsAffine X₀ →
      ∀ F₀ : Sheaf T₀.smallEtaleTopology (Type (max (u + 1) v)),
        IsIso ((smallEtaleSetsBaseChange.{u, v} e₀ h₀ g₀ f₀ sq₀.w.symm).app F₀))
    (i : (affineOpenBaseChangeData.{v} f h e g sq F).I) :
    IsIso ((smallEtaleSetsBaseChange.{u, v}
      ((affineOpenBaseChangeData.{v} f h e g sq F).e_i i)
      ((affineOpenBaseChangeData.{v} f h e g sq F).h_i i)
      ((affineOpenBaseChangeData.{v} f h e g sq F).g_i i)
      ((affineOpenBaseChangeData.{v} f h e g sq F).f_i i)
      (((affineOpenBaseChangeData.{v} f h e g sq F).local_cartesian i).w.symm)).app
        ((smallEtaleInverseImage.{u, v}
          ((affineOpenBaseChangeData.{v} f h e g sq F).toT_i i)).obj
            (affineOpenBaseChangeData.{v} f h e g sq F).F)) :=
  haff _ _ _ _ _ _ _ _ ((affineOpenBaseChangeData.{v} f h e g sq F).local_cartesian i) rfl
    (isAffine_affineOpenBaseChangeData_U.{v} f h e g sq F i) _

/-- **Base change for the direct images of sheaves of sets is Zariski-local on `X`**, in the
spelling of Tag 0EZR: the content of
`Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isAffine_case`, before the two spellings
of the base change map are identified. -/
private theorem isIso_smallEtaleSetsBaseChange_of_isAffine_case (f : X ⟶ S) (h : Y ⟶ X)
    (e : Y ⟶ T) (g : T ⟶ S) (sq : IsPullback h e f g)
    (F : Sheaf T.smallEtaleTopology (Type (max (u + 1) v)))
    (haff : ∀ (X₀ Y₀ S₀ T₀ : Scheme.{u}) (f₀ : X₀ ⟶ S₀) (h₀ : Y₀ ⟶ X₀) (e₀ : Y₀ ⟶ T₀)
      (g₀ : T₀ ⟶ S₀) (sq₀ : IsPullback h₀ e₀ f₀ g₀), S₀ = S → IsAffine X₀ →
      ∀ F₀ : Sheaf T₀.smallEtaleTopology (Type (max (u + 1) v)),
        IsIso ((smallEtaleSetsBaseChange.{u, v} e₀ h₀ g₀ f₀ sq₀.w.symm).app F₀)) :
    IsIso ((smallEtaleSetsBaseChange.{u, v} e h g f sq.w.symm).app F) := by
  have generic : ∀ {X₀ Y₀ S₀ T₀ : Scheme.{u}} (e₀ : Y₀ ⟶ T₀) (h₀ : Y₀ ⟶ X₀) (g₀ : T₀ ⟶ S₀)
      (f₀ : X₀ ⟶ S₀) (w₀ : e₀ ≫ g₀ = h₀ ≫ f₀)
      (F₀ : Sheaf T₀.smallEtaleTopology (Type (max (u + 1) v)))
      (D : EtaleLocalBaseChangeData.{u, u, _, _} (Type (max (u + 1) v))),
      X₀ = D.X → Y₀ = D.Y → S₀ = D.S → T₀ = D.T → HEq e₀ D.e → HEq h₀ D.h → HEq g₀ D.g →
      HEq f₀ D.f → HEq F₀ D.F →
      (∀ i, IsIso ((smallEtaleSetsBaseChange.{u, v} (D.e_i i) (D.h_i i) (D.g_i i) (D.f_i i)
        (D.local_cartesian i).w.symm).app
          ((smallEtaleInverseImage.{u, v} (D.toT_i i)).obj D.F))) →
      IsIso ((smallEtaleSetsBaseChange.{u, v} e₀ h₀ g₀ f₀ w₀).app F₀) := by
    intro X₀ Y₀ S₀ T₀ e₀ h₀ g₀ f₀ w₀ F₀ D hX hY hS hT he hh hg hf hF hlocal
    subst hX
    subst hY
    subst hS
    subst hT
    obtain rfl := eq_of_heq he
    obtain rfl := eq_of_heq hh
    obtain rfl := eq_of_heq hg
    obtain rfl := eq_of_heq hf
    obtain rfl := eq_of_heq hF
    have hww : w₀ = D.cartesian.w.symm := rfl
    subst hww
    exact isIso_smallEtaleSetsBaseChange_app_of_isIso_local D hlocal
  exact generic e h g f sq.w.symm F (affineOpenBaseChangeData.{v} f h e g sq F)
    rfl rfl rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
    (isIso_smallEtaleSetsBaseChange_affineOpenBaseChangeData_local.{v} f h e g sq F haff)

/-- **Base change for the direct images of sheaves of sets is Zariski-local on `X`.** Let

```
X <--h-- Y
|f       |e
S <--g-- T
```

be a cartesian square of schemes and let `F` be a sheaf of sets on the small étale site of `T`.
If the base change map `f_0^{-1}g_{0, *}F_0 ⟶ h_{0, *}e_0^{-1}F_0` is an isomorphism for every
cartesian square

```
X₀ <--h₀-- Y₀
|f₀        |e₀
S  <--g₀-- T₀
```

over the same `S` whose upper left corner `X₀` is affine and every sheaf `F₀` of sets on the
small étale site of `T₀`, then the base change map `f^{-1}g_*F ⟶ h_*e^{-1}F` of the given square
is an isomorphism.

The covering to which Tag 0EZR clause (1) is applied is the Zariski covering of `X` by its
affine opens, through `Stacks.EtaleCohomology.affineOpenBaseChangeData`; the `i`-th local square
is then the base change of the given square along the open immersion `U ⟶ X`, with the same
base `S`, and its upper left corner is affine by choice of the covering. -/
theorem isIso_smallEtaleSetBaseChange_of_isAffine_case (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T)
    (g : T ⟶ S) (sq : IsPullback h e f g)
    (F : Sheaf T.smallEtaleTopology (Type (max (u + 1) v)))
    (haff : ∀ (X₀ Y₀ T₀ : Scheme.{u}) (f₀ : X₀ ⟶ S) (h₀ : Y₀ ⟶ X₀) (e₀ : Y₀ ⟶ T₀) (g₀ : T₀ ⟶ S)
      (sq₀ : IsPullback h₀ e₀ f₀ g₀), IsAffine X₀ →
      ∀ F₀ : Sheaf T₀.smallEtaleTopology (Type (max (u + 1) v)),
        IsIso ((smallEtaleSetBaseChange.{u, v} e₀ h₀ g₀ f₀ sq₀.w.symm).app F₀)) :
    IsIso ((smallEtaleSetBaseChange.{u, v} e h g f sq.w.symm).app F) :=
  isIso_smallEtaleSetBaseChange_of_isIso_smallEtaleSetsBaseChange.{v} _ _ _ _ _ _
    (isIso_smallEtaleSetsBaseChange_of_isAffine_case.{v} f h e g sq F
      fun X₀ Y₀ S₀ T₀ f₀ h₀ e₀ g₀ sq₀ hS₀ hX₀ F₀ => by
        subst hS₀
        exact isIso_smallEtaleSetsBaseChange_of_isIso_smallEtaleSetBaseChange.{v} _ _ _ _ _ _
          (haff X₀ Y₀ T₀ f₀ h₀ e₀ g₀ sq₀ hX₀ F₀))

end AffineLocality

end Stacks.EtaleCohomology

end
