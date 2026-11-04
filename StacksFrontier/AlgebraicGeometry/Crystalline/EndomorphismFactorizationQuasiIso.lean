module

public import Mathlib.Algebra.Category.Grp.AB
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.RelativePoincare

/-!
# A factored endomorphism of a complex is a quasi-isomorphism

The proof of [Stacks, Lemma 60.21.4, Tag 07LH] ends with a claim about an arbitrary divided
power `A`-algebra endomorphism `ρ : D → D` compatible with the augmentation to `C`: the induced
map `M ⊗^∧_D Ω^*_D → M ⊗^∧_{D, ρ} Ω^*_D` is a quasi-isomorphism.  The source proves it by
factoring `ρ` through the `p`-adic completion of a divided power polynomial algebra,

`D --σ--> D⟨ξ_i⟩^∧ --τ--> D`,  `σ(x_i) = x_i + ξ_i`,  `τ(ξ_i) = z_i`,

where `ρ(x_i) = x_i + z_i` and the `z_i` lie in the divided power ideal, and then observing
three things.  There is an automorphism `α` of `D⟨ξ_i⟩^∧` with `α(x_i) = x_i - ξ_i` and
`α(ξ_i) = ξ_i`, so `α ∘ σ` is the structure map `ν : D → D⟨ξ_i⟩^∧`, `x_i ↦ x_i`; `τ ∘ ν` is the
identity of `D`; and the map induced by `ν` is a quasi-isomorphism, which is the **completed
clause of [Stacks, Lemma 60.20.2, Tag 07LD]**.

This module is that argument, and nothing else, at the level of complexes of abelian groups: it
is homological algebra with the divided powers removed.  Keeping it separate is what makes it
checkable — each of the three observations above becomes one hypothesis about honest morphisms
of complexes, and the conclusion follows by the functoriality of `homologyMap` alone.

## Main results

* `Crystalline.CompletedDeRham.isIso_homologyMap_of_homotopyRetract` — a homotopy equivalence of
  complexes of abelian groups is invertible on homology.
* `Crystalline.CompletedDeRham.isIso_homologyMap_of_degreewiseHomotopyRetract` — the same with the
  homotopy given as a degree-lowering family and the two contraction identities, which is the
  shape `Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` produces.
* `Crystalline.CompletedDeRham.isIso_homologyMap_isoHom`,
  `Crystalline.CompletedDeRham.isIso_homologyMap_left_of_comp_eq` — the two pieces of
  functoriality the factorization step is assembled from.
* `Crystalline.CompletedDeRham.isIso_homologyMap_of_transport` — **the factorization step**: an
  endomorphism that factors as above is invertible on homology.  The three maps of the source's
  argument land in *two* complexes, related by a transport `T`, which is the shape in which the
  factorization actually occurs; see "Why the transport" below.
* `Crystalline.CompletedDeRham.isIso_homologyMap_of_transport_iso` — the same with the transport
  given as an isomorphism of complexes rather than as a map invertible on homology.
* `Crystalline.CompletedDeRham.isIso_homologyMap_of_factorization` — a form of the
  factorization step in which `s` and `incl` are required to land in the *same* complex and the
  transport is an endomorphism of it.  **Its hypotheses cannot be met by the source's data**, for
  the reason set out below; it is superseded by
  `...isIso_homologyMap_of_transport`.

## Why the transport

In the application the three maps of the source's argument are base changes of the completed de
Rham complex of `(M, ∇)` along three different ring maps, and base change along `D → E` changes
the *module*: it is `M ⊗̂_D E`, whose `D`-action on `E` is the `Algebra D E` instance, so base
changing along two different maps `D → E` produces two genuinely different modules and hence two
genuinely different complexes.  Here `s` is the base change along `σ`, into the complex of
`M ⊗̂_{D, σ} D⟨ξ_i⟩^∧`, while `incl` is the base change along `ν`, into the complex of
`M ⊗̂_{D, ν} D⟨ξ_i⟩^∧`; the identity `α ∘ σ = ν` relates them, and `α` is *not* an automorphism of
either one — on the coefficient ring `α ∘ ν` is `σ⁻`, which sends `x_i` to `x_i - ξ_i`, and not
`ν`, by `Crystalline.envelopeCompletionAlpha_comp_nu`.  So the transport `T` goes between two
complexes, and the retraction `t` is taken out of the first of them.

This matters beyond bookkeeping.  Suppose, as in
`Crystalline.CompletedDeRham.isIso_homologyMap_of_factorization`, that `s` and `incl` are
required to be maps into one complex `Y` and `t : Y ⟶ X` a single map out of it.  If all three
are base changes along ring maps then `s` and `incl` are base changes along one and the same map
`w : D → E` — the one that the module `M ⊗̂_D E` common to their targets is formed along — and
`t` is a base change along one map `c : E → D`.  Then `s ≫ t` and `incl ≫ t` are both the base
change along `c ∘ w`, so `incl ≫ t = 𝟙` forces `c ∘ w = id_D` while `s ≫ t = ρ` forces
`c ∘ w = ρ`, and `ρ` is not the identity.  The hypotheses of that earlier form are therefore
jointly unsatisfiable by the source's data, which is why it is superseded rather than used.

## The shape of the results

`Crystalline.CompletedDeRham.isIso_homologyMap_of_homotopyRetract` is the consumer of
[Stacks, Tag 07LD] as this library proves it.  The completed clause with a module and a
connection is `Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedDeRhamPerturbation.lean`, which produces
more than a quasi-isomorphism: a map `ι'` with a retraction `π'`, `π' ι' = 1`, and a chain
homotopy from `ι' π'` to the identity.  That is a homotopy equivalence, and this lemma turns it
into invertibility on homology in each degree.  Both halves are needed and neither alone
suffices: `π' ι' = 1` gives only that `H(ι')` is split injective, and a homotopy alone gives
nothing without a map to be homotopic to.

`Crystalline.CompletedDeRham.isIso_homologyMap_of_transport` is the factorization step.  Note
which way the composites run: base change along a ring map `D → E` takes complexes over `D` to
complexes over `E`, so base change along `τ ∘ σ` is base change along `σ` **followed by** base
change along `τ`.  Its hypotheses are: `hfac`, that the endomorphism under study is the one
induced by `τ ∘ σ`; `hsT`, that the transport carries `s` to `incl`, which is `α ∘ σ = ν`; `hT`,
that the transport is invertible on homology, which is "using that `α` is an isomorphism";
`hincl`, [Stacks, Tag 07LD] for `ν`; and `ht`, that the retraction `t` is invertible on homology.

`ht` is the one hypothesis with no single sentence of the source behind it.  The source's
sentence "the map `τ` has as a left inverse the map `D → D⟨x_i⟩^∧`, `x_i ↦ x_i`" is about the
base change along `τ` out of the complex of `M ⊗̂_{D, ν} D⟨ξ_i⟩^∧` — the `ν` copy, where the
retraction `τ ∘ ν = id_D` lives — and that statement is proved, as
`Crystalline.isIso_homologyMap_tauComplexHom`.  The map `t` needed here is the base change along
`τ` out of the `σ` copy, where `τ ∘ σ = ρ` and no section comes from a ring map; it is a
different map, and `H(s) ≫ H(t) = H(ρ)` makes any derivation of it from `H(s)` circular.  So it
is carried as a hypothesis.

The transport `T` is not required to be an isomorphism of complexes, only to be invertible on
homology, because that is all the argument uses and all that is available: in the application
`T` is the base change along `α` followed by the comparison of the twice base-changed module with
the once base-changed one, and only the second factor is known to be an isomorphism.  Nothing
about `α` being a *ring* automorphism is needed once it is read on the complexes.

## What this does not do

No result here mentions divided powers, so none carries a Stacks tag.  In particular nothing here
proves [Stacks, Tag 07LD]: `hincl` is a hypothesis, and the work of producing the complexes for
`D⟨ξ_i⟩^∧` and the maps into and out of them is done elsewhere.  Neither is `ht` proved here, nor
anywhere in this library; see above.

## References

* [Stacks Project, Lemma 60.21.4, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
* [Stacks Project, Lemma 60.20.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Crystalline

namespace CompletedDeRham

section FactoredQuasiIso

variable {X Y Y₁ Y₂ Z : CochainComplex AddCommGrpCat.{u} ℕ}

/-- Homology maps of composites that are the identity compose to the identity. -/
private theorem homologyMap_comp_eq_id {W : CochainComplex AddCommGrpCat.{u} ℕ} (f : X ⟶ W)
    (g : W ⟶ X) (h : f ≫ g = 𝟙 X) (j : ℕ) :
    HomologicalComplex.homologyMap f j ≫ HomologicalComplex.homologyMap g j = 𝟙 _ := by
  rw [← HomologicalComplex.homologyMap_comp, h, HomologicalComplex.homologyMap_id]

/-- **A homotopy equivalence of complexes of abelian groups is invertible on homology.**

Given `ι : X ⟶ Y` with a retraction `π : Y ⟶ X`, so that `ι ≫ π = 𝟙 X` on the nose, and a chain
homotopy from `π ≫ ι` to `𝟙 Y`, the map `HomologicalComplex.homologyMap ι j` is an isomorphism
for every `j`; its inverse is `HomologicalComplex.homologyMap π j`.

This is the shape in which [Stacks, Lemma 60.20.2, Tag 07LD] is proved in this library:
`Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` produces exactly `ι'`, `π'`, the
identity `π' ι' = 1` and the homotopy, so this lemma is how that output is read as the source's
quasi-isomorphism.  The strict identity on one side and the homotopy on the other are not
interchangeable here: `homologyMap` is functorial, which turns the identity into one of the two
inverse laws, and homotopic maps have equal maps on homology, which turns the homotopy into the
other. -/
theorem isIso_homologyMap_of_homotopyRetract (iota : X ⟶ Y) (pi : Y ⟶ X)
    (hretract : iota ≫ pi = 𝟙 X) (h : Homotopy (pi ≫ iota) (𝟙 Y)) (j : ℕ) :
    IsIso (HomologicalComplex.homologyMap iota j) := by
  refine ⟨⟨HomologicalComplex.homologyMap pi j, homologyMap_comp_eq_id iota pi hretract j, ?_⟩⟩
  · rw [← HomologicalComplex.homologyMap_comp, h.homologyMap_eq,
      HomologicalComplex.homologyMap_id]

/-- The map on homology induced by an isomorphism of complexes is an isomorphism, its inverse
being the map induced by the inverse. -/
theorem isIso_homologyMap_isoHom (e : X ≅ Y) (j : ℕ) :
    IsIso (HomologicalComplex.homologyMap e.hom j) :=
  ⟨⟨HomologicalComplex.homologyMap e.inv j, homologyMap_comp_eq_id _ _ e.hom_inv_id j,
    homologyMap_comp_eq_id _ _ e.inv_hom_id j⟩⟩

/-- **Cancelling an invertible right factor on homology.**  If `a ≫ b = c` and both `b` and `c`
are invertible on homology in a degree, so is `a`.

This is the one piece of functoriality the factorization step uses twice: once to pass from the
hypothesis about `incl` to the invertibility of `s` on homology, and once inside
`Crystalline.isIso_homologyMap_sigmaComplexHom`. -/
theorem isIso_homologyMap_left_of_comp_eq {W : CochainComplex AddCommGrpCat.{u} ℕ} (a : X ⟶ Y)
    (b : Y ⟶ W) (c : X ⟶ W) (habc : a ≫ b = c) (j : ℕ)
    (hb : IsIso (HomologicalComplex.homologyMap b j))
    (hc : IsIso (HomologicalComplex.homologyMap c j)) :
    IsIso (HomologicalComplex.homologyMap a j) := by
  have := hb
  have : IsIso (HomologicalComplex.homologyMap a j ≫ HomologicalComplex.homologyMap b j) := by
    rw [← HomologicalComplex.homologyMap_comp, habc]
    exact hc
  exact IsIso.of_isIso_comp_right (HomologicalComplex.homologyMap a j)
    (HomologicalComplex.homologyMap b j)

/-- **The factorization step of the proof of [Stacks, Lemma 60.21.4, Tag 07LH], in the shape the
factorization actually has.**

Let `rho : X ⟶ Z` be a map which factors as `s ≫ t` through a complex `Y₁`, let `T : Y₁ ⟶ Y₂` be
a *transport* carrying `s` to a second map `incl : X ⟶ Y₂`, and let `T`, `incl` and `t` each be
invertible on homology in every degree.  Then `rho` is invertible on homology in every degree.

The target `Z` is not required to be `X`.  In [Stacks, Tag 07LH] it is, the endomorphism there
being the composite `α ≫ β` of the two comparison maps, whose second factor carries the base
change back to `M ⊗̂_D Ω̂^*_D`; but the base change along `ρ` by itself lands in the complex of
`M ⊗̂_{D, ρ} Ω̂^*_D`, a different object, so the general target is what makes the lemma usable
directly at the envelope data as well.

This is the source's argument with the divided powers removed.  In the application `X` is
`M ⊗̂_D Ω̂^*_D`; `Y₁` is the completed de Rham complex of `M ⊗̂_{D, σ} D⟨ξ_i⟩^∧` and `Y₂` that of
`M ⊗̂_{D, ν} D⟨ξ_i⟩^∧`, which are *different* complexes because base change along two different
ring maps `D → D⟨ξ_i⟩^∧` produces two different modules; `s` and `t` are the base change maps
along `σ` and `τ`; `incl` is the base change map along the structure map `ν : D → D⟨ξ_i⟩^∧`; and
`T` is the automorphism `α` read on the complexes, composed with the comparison of the twice
base-changed module with the once base-changed one.  Then `hfac` is `τ ∘ σ = ρ`, `hsT` is
`α ∘ σ = ν`, `hT` is "`α` is an isomorphism", `hincl` is the completed clause of
[Stacks, Lemma 60.20.2, Tag 07LD] for `ν`, and `ht` is the invertibility on homology of the base
change along `τ` out of the `σ` copy.

The proof is two applications of the functoriality of `homologyMap`: from `hsT`, `hT` and
`hincl`, `H(s)` is invertible by
`Crystalline.CompletedDeRham.isIso_homologyMap_left_of_comp_eq`; from `hfac`, `H(rho)` is
`H(s) ≫ H(t)`.

`ht` is an input, not a consequence of the others.  The retraction `τ ∘ ν = id_D` of the source's
proof is a statement about the base change along `τ` out of `Y₂`, not out of `Y₁`; deriving `ht`
from `hfac` would need `H(rho)`, which is the conclusion. -/
theorem isIso_homologyMap_of_transport (rho : X ⟶ Z) (s : X ⟶ Y₁) (T : Y₁ ⟶ Y₂) (incl : X ⟶ Y₂)
    (t : Y₁ ⟶ Z) (hfac : s ≫ t = rho) (hsT : s ≫ T = incl)
    (hT : ∀ j : ℕ, IsIso (HomologicalComplex.homologyMap T j))
    (hincl : ∀ j : ℕ, IsIso (HomologicalComplex.homologyMap incl j))
    (ht : ∀ j : ℕ, IsIso (HomologicalComplex.homologyMap t j)) (j : ℕ) :
    IsIso (HomologicalComplex.homologyMap rho j) := by
  have := isIso_homologyMap_left_of_comp_eq s T incl hsT j (hT j) (hincl j)
  have := ht j
  rw [← hfac, HomologicalComplex.homologyMap_comp]
  infer_instance

/-- **The factorization step with the transport given as an isomorphism of complexes.**

This is `Crystalline.CompletedDeRham.isIso_homologyMap_of_transport` with `hT` replaced by the
stronger datum of an isomorphism `T : Y₁ ≅ Y₂`, which is how the transport reads when the
comparison it is built from is invertible on the nose rather than only on homology. -/
theorem isIso_homologyMap_of_transport_iso (rho : X ⟶ Z) (s : X ⟶ Y₁) (T : Y₁ ≅ Y₂)
    (incl : X ⟶ Y₂) (t : Y₁ ⟶ Z) (hfac : s ≫ t = rho) (hsT : s ≫ T.hom = incl)
    (hincl : ∀ j : ℕ, IsIso (HomologicalComplex.homologyMap incl j))
    (ht : ∀ j : ℕ, IsIso (HomologicalComplex.homologyMap t j)) (j : ℕ) :
    IsIso (HomologicalComplex.homologyMap rho j) :=
  isIso_homologyMap_of_transport rho s T.hom incl t hfac hsT
    (isIso_homologyMap_isoHom T) hincl ht j

/-- **An earlier shape of the factorization step of the proof of
[Stacks, Lemma 60.21.4, Tag 07LH], superseded by
`Crystalline.CompletedDeRham.isIso_homologyMap_of_transport`.**

Let `rho : X ⟶ X` be an endomorphism of a complex which factors as `s ≫ t` through a complex `Y`,
let `incl : X ⟶ Y` be a second map into `Y` which differs from `s` by an isomorphism `e` of `Y`
in the sense that `s ≫ e.hom = incl`, let `t` be a retraction of `incl`, and let `incl` be
invertible on homology in every degree.  Then `rho` is invertible on homology in every degree.

The statement is true, and is proved below from the functoriality of `homologyMap`: from `hse`,
`H(s)` is `H(incl)` composed with the inverse of `H(e.hom)`, hence invertible; from `hit`, `H(t)`
is the inverse of `H(incl)`, hence invertible; from `hfac`, `H(rho)` is `H(s) ≫ H(t)`.

**It is nevertheless not the factorization step of the source's proof**, because its hypotheses
cannot be met by the source's data.  Requiring `s` and `incl` to be maps into one complex `Y`,
and `t` to be a single map out of it, forces — when all three are base changes along ring maps —
`s` and `incl` to be base changes along the same map `w : D → E`, since the module `M ⊗̂_D E`
their common target is built from is formed along one `Algebra D E` instance; and then `s ≫ t`
and `incl ≫ t` are both the base change along `c ∘ w`, where `c` is the map `t` is a base change
along.  So `hit` says `c ∘ w = id_D` and `hfac` says `c ∘ w = ρ`, which cannot both hold for
`ρ ≠ id`.  In the source `s` is the base change along `σ` and `incl` the base change along `ν`,
two different maps `D → D⟨ξ_i⟩^∧`, so their targets are two different complexes and `α` is a
transport between them rather than an automorphism of one — already on the coefficient ring
`α ∘ ν` is `σ⁻` and not `ν`, by `Crystalline.envelopeCompletionAlpha_comp_nu`.

`Crystalline.CompletedDeRham.isIso_homologyMap_of_transport` is the correct statement; this one
should not be used. -/
theorem isIso_homologyMap_of_factorization (rho : X ⟶ X) (s : X ⟶ Y) (t : Y ⟶ X)
    (incl : X ⟶ Y) (e : Y ≅ Y) (hfac : s ≫ t = rho) (hse : s ≫ e.hom = incl)
    (hit : incl ≫ t = 𝟙 X)
    (hincl : ∀ j : ℕ, IsIso (HomologicalComplex.homologyMap incl j)) (j : ℕ) :
    IsIso (HomologicalComplex.homologyMap rho j) := by
  have := hincl j
  have hs : IsIso (HomologicalComplex.homologyMap s j) :=
    isIso_homologyMap_left_of_comp_eq s e.hom incl hse j (isIso_homologyMap_isoHom e j) (hincl j)
  have ht : IsIso (HomologicalComplex.homologyMap t j) := by
    rw [← IsIso.inv_eq_of_hom_inv_id (homologyMap_comp_eq_id incl t hit j)]
    infer_instance
  rw [← hfac, HomologicalComplex.homologyMap_comp]
  infer_instance

/-- **A degreewise homotopy retract of complexes of abelian groups is invertible on homology.**

This is `Crystalline.CompletedDeRham.isIso_homologyMap_of_homotopyRetract` stated at the data
`Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` actually produces: besides the chain
maps `ι`, `π` and the identity `ι ≫ π = 𝟙`, the homotopy is given as a family `H i` of
degree-lowering maps satisfying the degree-`0` identity `d ∘ H + ι π = 1` and the identity
`H ∘ d + d ∘ H + ι π = 1` in the degrees above — which is the shape of the last two conjuncts of
that theorem's conclusion, one `AddCommGrpCat.ext` away.

Nothing is assumed about `H` beyond those two identities; in particular it is not assumed to
square to zero or to be compatible with `ι` and `π`, which the perturbation lemma's own `ĥ` is
but which plays no part here.  The passage from the degreewise family to Mathlib's doubly
indexed `Homotopy` is `Crystalline.cochainHomotopyOfDegreewise`, already in this library for the
uncompleted Poincaré lemma; only the sign is new, the contraction identities being stated with
`ι π` on the left and the identity on the right. -/
theorem isIso_homologyMap_of_degreewiseHomotopyRetract (iota : X ⟶ Y) (pi : Y ⟶ X)
    (hh : ∀ i, Y.X (i + 1) ⟶ Y.X i) (hretract : iota ≫ pi = 𝟙 X)
    (h0 : Y.d 0 (0 + 1) ≫ hh 0 + pi.f 0 ≫ iota.f 0 = 𝟙 (Y.X 0))
    (hsucc : ∀ i : ℕ, Y.d (i + 1) (i + 1 + 1) ≫ hh (i + 1) + hh i ≫ Y.d i (i + 1) +
      pi.f (i + 1) ≫ iota.f (i + 1) = 𝟙 (Y.X (i + 1))) (j : ℕ) :
    IsIso (HomologicalComplex.homologyMap iota j) :=
  isIso_homologyMap_of_homotopyRetract iota pi hretract
    (cochainHomotopyOfDegreewise (f := pi ≫ iota) (g := 𝟙 Y) (fun i ↦ -hh i)
      (by
        simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, Preadditive.comp_neg]
        rw [← h0]
        abel)
      (fun i ↦ by
        simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, Preadditive.comp_neg,
          Preadditive.neg_comp]
        rw [← hsucc i]
        abel))
    j

end FactoredQuasiIso

end CompletedDeRham

end Crystalline

end
