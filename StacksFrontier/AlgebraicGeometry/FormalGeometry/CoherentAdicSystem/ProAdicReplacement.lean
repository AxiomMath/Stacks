module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Kernel
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.KernelCokernelAnnihilation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.MorphismGluing
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientMap
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.TwoIdealAdicQuotient
public import StacksFrontier.AlgebraicGeometry.ProperMapping
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.PullbackIdealPower
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.PullbackEquivalence
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.Zariski
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Epi
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SequentialProIsomorphismSymm

/-!
# Pro-adic replacement: a pro-system locally pro-isomorphic to coherent adic systems

Let `X` be a Noetherian scheme, `ℐ` a quasi-coherent ideal sheaf on `X` and `(Pₙ)` an inverse
system of coherent `𝒪_X`-modules. Suppose that every point of `X` has an open neighbourhood `U`
on which `(Pₙ|_U)` is pro-isomorphic to an object of `Coh(U, ℐ|_U)`. Then `(Pₙ)` is
pro-isomorphic to an object `(Hₙ)` of `Coh(X, ℐ)`; a map `(Fₙ) ⟶ (Pₙ)` out of an object of
`Coh(X, ℐ)` induces a morphism `(Fₙ) ⟶ (Hₙ)`; and on every open `U` the restriction of `(Hₙ)` is,
compatibly with these maps, isomorphic to every object of `Coh(U, ℐ|_U)` pro-isomorphic to
`(Pₙ|_U)`. This is the gluing step of the proofs of [Stacks, Tag 0EJE], [Stacks, Tag 0EJF] and
[Stacks, Tag 0EJG], which construct the replacement affine-locally.

## The construction

The replacement is cut out of `(Pₙ)` itself, so that nothing has to be glued. Given levels
`n ≤ m n ≤ k n`, monotone in `n` (`Stacks.Coherent.ReplacementLevels`), its term of index `n` is
the image of the reduction

`P_{k n} ⟶ P_{m n} ⟶ P_{m n} / ℐ ⁿ⁺¹ P_{m n}`,

and its transition maps are induced by the maps between these quotients
(`Stacks.Coherent.replacementSystem`). On an open `U` carrying a pro-isomorphism
`(φ, ψ) : (Pₙ|_U) ≅ (Nₙ)` with an object of `Coh(U, ℐ|_U)`, and for levels large compared with the
reindexings of the pro-isomorphism (`Stacks.Coherent.LocalProAdicDatum.Fits`), the restricted
reduction factors as an epimorphism `P_{k n}|_U ⟶ Nₙ` followed by a split monomorphism
`Nₙ ⟶ P_{m n}/ℐ ⁿ⁺¹ P_{m n}|_U`; so the restriction of the image is `Nₙ`, compatibly with the
transition maps. A Noetherian scheme is quasi-compact, so finitely many such opens cover `X` and
one choice of levels serves all of them. Being a coherent adic system is then checked locally:
the terms are coherent and annihilated by `ℐ ⁿ⁺¹` globally, and the comparison
`Hₙ₊₁ / ℐ ⁿ⁺¹ Hₙ₊₁ ⟶ Hₙ` is an isomorphism because it is so on every member of the cover.

The maps back `H_{β n} ⟶ Pₙ` of the pro-isomorphism are obtained by descending a transition map
of `(Pₙ)` along the epimorphism `P_{k(β n)} ⟶ H_{β n}`; that the kernel is killed is again
checked locally, where it follows from the backward maps of the local pro-isomorphisms.

## Main definitions

* `Stacks.Coherent.replacementSystem` — the inverse system cut out of `(Pₙ)` at given levels.
* `Stacks.Coherent.replacementProIso` — the pro-isomorphism with `(Pₙ)` given maps back.
* `Stacks.Coherent.replacementLift` — the map into the replacement induced by a map out of an
  object of `Coh(X, ℐ)`.
* `Stacks.Coherent.isoOfProIso` — the isomorphism of coherent adic systems induced by a
  pro-isomorphism.

## Main results

* `Stacks.Coherent.exists_coherentAdicReplacement` — the replacement theorem described above.
* `Stacks.Coherent.isCoherentAdicSystem_replacementSystem` — the replacement attached to a cover
  by local data is a coherent adic system.
* `Stacks.Coherent.epi_of_epi_restrictFunctor_map` — surjectivity in `Coh(X, ℐ)` is local on
  `X`. (Locality of the annihilation of levelwise kernels and cokernels by a power of an ideal is
  `Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_of_restrict`.)

## Implementation notes

Pro-isomorphisms are `InverseSequence.ProIso`, the explicit up-to-refinement form. The image is
`CategoryTheory.Abelian.image`, so that its coherence is
`Stacks.AlgebraicGeometry.ProperMapping.isCoherent_image_modules`. The local comparison is the
uniqueness of epi-mono factorizations in an abelian category,
`Stacks.Coherent.exists_iso_of_epi_mono_fac`.

## References

* [Stacks Project, Tag 0EJE](https://stacks.math.columbia.edu/tag/0EJE)
* [Stacks Project, Tag 0EJF](https://stacks.math.columbia.edu/tag/0EJF)
* [Stacks Project, Tag 0EJG](https://stacks.math.columbia.edu/tag/0EJG)
* [Stacks Project, Tag 0EIQ](https://stacks.math.columbia.edu/tag/0EIQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization

universe u

namespace Stacks.Coherent

/-- The zero morphism out of the sheaf of modules underlying a subsheaf, as in
`Stacks.Algebraization.submodule_ι_comp_eq_zero_iff`. -/
local instance zeroHomOfSubmoduleSheaf {Y : Scheme.{u}} (A : SheafOfModules.{u} Y.ringCatSheaf)
    (B : Y.Modules) : Zero (A ⟶ B) :=
  HasZeroMorphisms.zero (C := Y.Modules) A B

section Adic

variable {Y : Scheme.{u}} (J : Y.IdealSheafData)

/-- A morphism into a module annihilated by `𝒥 ˢ` kills `𝒥 ʳ M` for every `r ≥ s`. -/
theorem idealPowerMultiple_ι_comp_eq_zero {M N : Y.Modules} (f : M ⟶ N) {r s : ℕ}
    (hrs : s ≤ r) (hN : idealPowerMultiple J s N = ⊥) :
    (idealPowerMultiple J r M).ι ≫ f = 0 := by
  have h : idealPowerMultiple J r M ≤ kernelSubmodule f := by
    have := idealPowerMultiple_le_sheafSubmoduleComap_of_pow_le (I := J) (J := J)
      (Scheme.IdealSheafData.pow_le_pow_of_le J hrs) f
    rwa [hN] at this
  refine (submodule_ι_comp_eq_zero_iff _ f).mpr fun U x hx => ?_
  have hx' := SheafOfModules.Submodule.le_iff.mp h U hx
  rwa [kernelSubmodule_toSubmodule_obj] at hx'

variable {J}

/-- The transition map of a system over `ℕᵒᵖ` for a composite `a ≤ b ≤ c` is the composite of the
transition maps. -/
private theorem map_homOfLE_op_comp {C : Type*} [Category C] (D : ℕᵒᵖ ⥤ C) {a b c : ℕ}
    (h : a ≤ b) (h' : b ≤ c) (h'' : a ≤ c) :
    D.map (homOfLE h'').op = D.map (homOfLE h').op ≫ D.map (homOfLE h).op := by
  rw [← D.map_comp]; rfl

/-- The transition map of a system over `ℕᵒᵖ` from an index to itself is the identity. -/
private theorem map_homOfLE_op_refl {C : Type*} [Category C] (D : ℕᵒᵖ ⥤ C) {a : ℕ} (h : a ≤ a) :
    D.map (homOfLE h).op = 𝟙 _ :=
  D.map_id _

/-- The transition maps of a coherent adic system are epimorphisms. -/
theorem epi_map_of_isCoherentAdicSystem {D : ℕᵒᵖ ⥤ Y.Modules} (hD : IsCoherentAdicSystem J D)
    {a b : ℕ} (h : a ≤ b) : Epi (D.map (homOfLE h).op) := by
  induction b, h using Nat.le_induction with
  | base => rw [map_homOfLE_op_refl]; infer_instance
  | succ b hab ih =>
    obtain ⟨e, he⟩ := hD.2.2 b
    rw [map_homOfLE_op_comp D hab (Nat.le_succ b), ← he]
    exact epi_comp' (epi_comp' (epi_cokernel_π_submodule_ι _) (IsIso.epi_of_iso e.hom)) ih

/-- A morphism out of a term of a coherent adic system into a module annihilated by `𝒥 ᵃ⁺¹`
factors through the transition map to the term of index `a`. -/
theorem exists_desc_of_isCoherentAdicSystem {D : ℕᵒᵖ ⥤ Y.Modules}
    (hD : IsCoherentAdicSystem J D) {a b : ℕ} (h : a ≤ b) {M : Y.Modules}
    (f : D.obj (op b) ⟶ M) (hM : idealPowerMultiple J (a + 1) M = ⊥) :
    ∃ g : D.obj (op a) ⟶ M, D.map (homOfLE h).op ≫ g = f := by
  induction b, h using Nat.le_induction with
  | base => exact ⟨f, by rw [map_homOfLE_op_refl, Category.id_comp]⟩
  | succ b hab ih =>
    obtain ⟨e, he⟩ := hD.2.2 b
    have hz := idealPowerMultiple_ι_comp_eq_zero J f (Nat.succ_le_succ hab) hM
    obtain ⟨g, hg⟩ := ih (e.inv ≫ cokernel.desc _ f hz)
    refine ⟨g, ?_⟩
    rw [map_homOfLE_op_comp D hab (Nat.le_succ b), Category.assoc, hg, ← he]
    exact (Category.assoc (obj := Y.Modules) _ _ _).trans
      ((congrArg (fun t => cokernel.π (C := Y.Modules) _ ≫ t) (e.hom_inv_id_assoc _)).trans
        (cokernel.π_desc _ _ _))

end Adic

section Construction

variable {X : Scheme.{u}} (I : X.IdealSheafData) (P : ℕᵒᵖ ⥤ X.Modules)

/-- The levels at which the pro-adic replacement of an inverse system is cut out: the term of
index `n` is the image of `P_{k n}` in `P_{m n} / ℐ ⁿ⁺¹ P_{m n}`. -/
structure ReplacementLevels where
  /-- The level of the quotient. -/
  m : ℕ → ℕ
  /-- The level of the source. -/
  k : ℕ → ℕ
  /-- The quotient level is monotone. -/
  mono_m : Monotone m
  /-- The source level is monotone. -/
  mono_k : Monotone k
  /-- The quotient level is at least the index. -/
  le_m : ∀ n, n ≤ m n
  /-- The source level is at least the quotient level. -/
  m_le_k : ∀ n, m n ≤ k n

variable (L : ReplacementLevels)

/-- The quotient `P_{m n} / ℐ ⁿ⁺¹ P_{m n}`. -/
abbrev replacementQuotient (n : ℕ) : X.Modules :=
  idealPowerQuotient I (n + 1) (P.obj (op (L.m n)))

/-- The reduction `P_{k n} ⟶ P_{m n} / ℐ ⁿ⁺¹ P_{m n}`. -/
def replacementReduction (n : ℕ) : P.obj (op (L.k n)) ⟶ replacementQuotient I P L n :=
  P.map (homOfLE (L.m_le_k n)).op ≫
    cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) (P.obj (op (L.m n)))).ι

/-- The map between consecutive quotients. -/
def replacementDrop (n : ℕ) : replacementQuotient I P L (n + 1) ⟶ replacementQuotient I P L n :=
  idealPowerQuotientMap I I (n + 1 + 1) (n + 1)
    (Scheme.IdealSheafData.pow_le_pow_of_le I (Nat.le_succ _))
    (P.map (homOfLE (L.mono_m (Nat.le_succ n))).op)

/-- The reductions are compatible with the transition maps: the reduction at index `n + 1` followed
by the map `P_{m(n+1)} / ℐ ⁿ⁺² P_{m(n+1)} ⟶ P_{m n} / ℐ ⁿ⁺¹ P_{m n}` is the transition map
`P_{k(n+1)} ⟶ P_{k n}` followed by the reduction at index `n`. -/
theorem replacementReduction_comp_drop (n : ℕ) :
    replacementReduction I P L (n + 1) ≫ replacementDrop I P L n =
      P.map (homOfLE (L.mono_k (Nat.le_succ n))).op ≫ replacementReduction I P L n := by
  rw [replacementReduction, replacementReduction, replacementDrop, Category.assoc,
    idealPowerQuotientMap_π, ← Category.assoc, ← Category.assoc, ← P.map_comp, ← P.map_comp]
  rfl

/-- The term of index `n` of the replacement: the image of the reduction. -/
abbrev replacementTerm (n : ℕ) : X.Modules := Abelian.image (replacementReduction I P L n)

/-- The image of the reduction at index `n + 1`, mapped to `P_{m n} / ℐ ⁿ⁺¹ P_{m n}`, is killed by
the cokernel of the reduction at index `n`. -/
theorem replacementTransition_aux (n : ℕ) :
    Abelian.image.ι (replacementReduction I P L (n + 1)) ≫ replacementDrop I P L n ≫
      cokernel.π (replacementReduction I P L n) = 0 := by
  rw [← cancel_epi (Abelian.factorThruImage (replacementReduction I P L (n + 1))),
    ← Category.assoc, Abelian.image.fac, ← Category.assoc, replacementReduction_comp_drop,
    Category.assoc, cokernel.condition, comp_zero, comp_zero]

/-- The transition map of the replacement. -/
def replacementTransition (n : ℕ) :
    replacementTerm I P L (n + 1) ⟶ replacementTerm I P L n :=
  kernel.lift _ (Abelian.image.ι (replacementReduction I P L (n + 1)) ≫
    replacementDrop I P L n) (by rw [Category.assoc]; exact replacementTransition_aux I P L n)

/-- The pro-adic replacement, as an inverse system. -/
def replacementSystem : ℕᵒᵖ ⥤ X.Modules :=
  Functor.ofOpSequence (replacementTransition I P L)

/-- The projection of `P_{k n}` onto the term of index `n`. -/
def replacementπ (n : ℕ) : P.obj (op (L.k n)) ⟶ (replacementSystem I P L).obj (op n) :=
  Abelian.factorThruImage (replacementReduction I P L n)

/-- The inclusion of the term of index `n` into `P_{m n} / ℐ ⁿ⁺¹ P_{m n}`. -/
def replacementι (n : ℕ) : (replacementSystem I P L).obj (op n) ⟶ replacementQuotient I P L n :=
  Abelian.image.ι (replacementReduction I P L n)

/-- The projection of `P_{k n}` onto the term of index `n` of the replacement is an epimorphism. -/
instance (n : ℕ) : Epi (replacementπ I P L n) :=
  inferInstanceAs (Epi (Abelian.factorThruImage _))

/-- The inclusion of the term of index `n` of the replacement into `P_{m n} / ℐ ⁿ⁺¹ P_{m n}` is a
monomorphism. -/
instance (n : ℕ) : Mono (replacementι I P L n) :=
  inferInstanceAs (Mono (Abelian.image.ι _))

/-- The projection of `P_{k n}` onto the term of index `n`, followed by the inclusion of that term
into `P_{m n} / ℐ ⁿ⁺¹ P_{m n}`, is the reduction. -/
theorem replacementπ_ι (n : ℕ) :
    replacementπ I P L n ≫ replacementι I P L n = replacementReduction I P L n :=
  Abelian.image.fac _

/-- Through the inclusions into the quotients, the transition map `H_{n+1} ⟶ H_n` of the
replacement is the map `P_{m(n+1)} / ℐ ⁿ⁺² P_{m(n+1)} ⟶ P_{m n} / ℐ ⁿ⁺¹ P_{m n}`. -/
theorem replacementMap_ι (n : ℕ) :
    (replacementSystem I P L).map (homOfLE (Nat.le_succ n)).op ≫ replacementι I P L n =
      replacementι I P L (n + 1) ≫ replacementDrop I P L n := by
  have h := Functor.ofOpSequence_map_homOfLE_succ (replacementTransition I P L) n
  refine (congrArg (fun t => t ≫ replacementι I P L n) h).trans ?_
  exact kernel.lift_ι _ _ _

/-- The projections onto consecutive terms of the replacement are compatible with the transition
maps `P_{k(n+1)} ⟶ P_{k n}` and `H_{n+1} ⟶ H_n`. -/
theorem replacementπ_map_succ (n : ℕ) :
    replacementπ I P L (n + 1) ≫ (replacementSystem I P L).map (homOfLE (Nat.le_succ n)).op =
      P.map (homOfLE (L.mono_k (Nat.le_succ n))).op ≫ replacementπ I P L n := by
  rw [← cancel_mono (replacementι I P L n), Category.assoc, replacementMap_ι,
    ← Category.assoc, replacementπ_ι, Category.assoc, replacementπ_ι,
    replacementReduction_comp_drop]

/-- The projections onto the terms of the replacement are compatible with the transition maps. -/
theorem replacementπ_map {a b : ℕ} (h : a ≤ b) :
    replacementπ I P L b ≫ (replacementSystem I P L).map (homOfLE h).op =
      P.map (homOfLE (L.mono_k h)).op ≫ replacementπ I P L a := by
  induction b, h using Nat.le_induction with
  | base =>
    rw [map_homOfLE_op_refl, map_homOfLE_op_refl, Category.comp_id, Category.id_comp]
  | succ b hab ih =>
    rw [map_homOfLE_op_comp _ hab (Nat.le_succ b),
      map_homOfLE_op_comp P (L.mono_k hab) (L.mono_k (Nat.le_succ b)), ← Category.assoc,
      replacementπ_map_succ, Category.assoc, ih, Category.assoc]

variable [∀ n, (P.obj n).IsCoherent]

/-- On a locally Noetherian scheme, every term of the replacement is coherent. -/
theorem isCoherent_replacementTerm [IsLocallyNoetherian X] (n : ℕ) :
    _root_.SheafOfModules.IsCoherent.{u} ((replacementSystem I P L).obj (op n)) :=
  Stacks.AlgebraicGeometry.ProperMapping.isCoherent_image_modules inferInstance
    (isCoherent_idealPowerQuotient I (n + 1) _) _

/-- The term of index `n` of the replacement is annihilated by `ℐ ⁿ⁺¹`. -/
theorem idealPowerMultiple_replacementTerm_eq_bot (n : ℕ) :
    idealPowerMultiple I (n + 1) ((replacementSystem I P L).obj (op n)) = ⊥ := by
  have : (P.obj (op (L.m n))).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  exact idealPowerMultiple_eq_bot_of_mono I (replacementι I P L n) (n + 1)
    (idealPowerMultiple_idealPowerQuotient_eq_bot I (n + 1) _)

/-! ### A pro-isomorphism from a left inverse up to refinement -/

variable {I P L}

/-- The pro-isomorphism between `P` and its replacement, given maps `ψₙ` back from the
replacement which, after the projections, are the transition maps of `P`. -/
def replacementProIso (β : ℕ → ℕ) (hβ : Monotone β) (hβle : ∀ n, n ≤ β n)
    (ψ : ∀ n, (replacementSystem I P L).obj (op (β n)) ⟶ P.obj (op n))
    (hψ : ∀ n, replacementπ I P L (β n) ≫ ψ n =
      P.map (homOfLE ((hβle n).trans ((L.le_m _).trans (L.m_le_k _)))).op) :
    InverseSequence.ProIso P (replacementSystem I P L) where
  α := L.k
  β := β
  αmono := L.mono_k
  βmono := hβ
  αle n := (L.le_m n).trans (L.m_le_k n)
  βle := hβle
  φ := replacementπ I P L
  ψ := ψ
  φnat h := (replacementπ_map I P L h).symm
  ψnat {m m'} h := by
    change (replacementSystem I P L).map _ ≫ ψ m = ψ m' ≫ P.map _
    rw [← cancel_epi (replacementπ I P L (β m')), ← Category.assoc, replacementπ_map,
      Category.assoc, hψ, ← Category.assoc, hψ, ← P.map_comp, ← P.map_comp]
    rfl
  ψφ n := hψ n
  φψ n := by
    change ψ (L.k n) ≫ replacementπ I P L n = (replacementSystem I P L).map _
    rw [← cancel_epi (replacementπ I P L (β (L.k n))), ← Category.assoc, hψ,
      replacementπ_map]

end Construction

/-! ### The replacement of a system pro-isomorphic to a coherent adic system -/

section Local

variable {Y : Scheme.{u}} {J : Y.IdealSheafData} {P : ℕᵒᵖ ⥤ Y.Modules}
  [∀ n, (P.obj n).IsCoherent] {L : ReplacementLevels} {N : CoherentAdicSystems J}
  (e : InverseSequence.ProIso P N.obj) (hm : ∀ n, e.α n ≤ L.m n)

omit [∀ n, (P.obj n).IsCoherent] in
include hm in
/-- The transition map `P_{m n} ⟶ P_{α n}` followed by the forward map `φ n : P_{α n} ⟶ N_n` of the
pro-isomorphism kills `𝒥 ⁿ⁺¹ P_{m n}`. -/
theorem replacementQuotient_desc_aux (n : ℕ) :
    (idealPowerMultiple J (n + 1) (P.obj (op (L.m n)))).ι ≫
      (P.map (homOfLE (hm n)).op ≫ e.φ n) = 0 :=
  idealPowerMultiple_ι_comp_eq_zero J _ le_rfl (N.property.2.1 n)

/-- The map `P_{m n} / 𝒥 ⁿ⁺¹ P_{m n} ⟶ N_n` induced by the pro-isomorphism. -/
def replacementQuotientToTerm (n : ℕ) : replacementQuotient J P L n ⟶ N.obj.obj (op n) :=
  cokernel.desc _ (P.map (homOfLE (hm n)).op ≫ e.φ n) (replacementQuotient_desc_aux e hm n)

/-- There is a map `g : N_n ⟶ P_{m n} / 𝒥 ⁿ⁺¹ P_{m n}` whose composite with the transition map
`N_{β(m n)} ⟶ N_n` is the backward map `ψ (m n) : N_{β(m n)} ⟶ P_{m n}` of the pro-isomorphism
followed by the projection onto the quotient. -/
theorem exists_termToReplacementQuotient (n : ℕ) :
    ∃ g : N.obj.obj (op n) ⟶ replacementQuotient J P L n,
      N.obj.map (homOfLE ((L.le_m n).trans (e.βle (L.m n)))).op ≫ g =
        e.ψ (L.m n) ≫ cokernel.π (C := Y.Modules)
          (idealPowerMultiple J (n + 1) (P.obj (op (L.m n)))).ι := by
  have : (P.obj (op (L.m n))).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  exact exists_desc_of_isCoherentAdicSystem N.property _ _
    (idealPowerMultiple_idealPowerQuotient_eq_bot J (n + 1) _)

/-- The map `N_n ⟶ P_{m n} / 𝒥 ⁿ⁺¹ P_{m n}` induced by the pro-isomorphism. -/
def termToReplacementQuotient (n : ℕ) : N.obj.obj (op n) ⟶ replacementQuotient J P L n :=
  (exists_termToReplacementQuotient e n).choose

/-- The composite of the transition map `N_{β(m n)} ⟶ N_n` with `termToReplacementQuotient` is the
backward map `ψ (m n)` of the pro-isomorphism followed by the projection onto
`P_{m n} / 𝒥 ⁿ⁺¹ P_{m n}`. -/
theorem termToReplacementQuotient_spec (n : ℕ) :
    N.obj.map (homOfLE ((L.le_m n).trans (e.βle (L.m n)))).op ≫
        termToReplacementQuotient e n =
      e.ψ (L.m n) ≫ cokernel.π (C := Y.Modules)
        (idealPowerMultiple J (n + 1) (P.obj (op (L.m n)))).ι :=
  (exists_termToReplacementQuotient e n).choose_spec

/-- `termToReplacementQuotient` followed by `replacementQuotientToTerm` is the identity of
`N_n`. -/
theorem termToReplacementQuotient_comp (n : ℕ) :
    termToReplacementQuotient e n ≫ replacementQuotientToTerm e hm n = 𝟙 _ := by
  have := epi_map_of_isCoherentAdicSystem N.property ((L.le_m n).trans (e.βle (L.m n)))
  rw [← cancel_epi (N.obj.map (homOfLE ((L.le_m n).trans (e.βle (L.m n)))).op),
    ← Category.assoc, termToReplacementQuotient_spec, Category.assoc, Category.comp_id]
  have h0 : cokernel.π (C := Y.Modules) (idealPowerMultiple J (n + 1) (P.obj (op (L.m n)))).ι ≫
      replacementQuotientToTerm e hm n = P.map (homOfLE (hm n)).op ≫ e.φ n :=
    cokernel.π_desc _ _ _
  rw [h0, ← Category.assoc]
  have h1 := e.ψnat (hm n)
  have h2 := e.φψ n
  simp only [InverseSequence.tr] at h1 h2
  rw [← h1, Category.assoc, h2, ← N.obj.map_comp]
  rfl

include hm in
/-- The map `N_n ⟶ P_{m n} / 𝒥 ⁿ⁺¹ P_{m n}` induced by the pro-isomorphism is a monomorphism. -/
theorem mono_termToReplacementQuotient (n : ℕ) : Mono (termToReplacementQuotient e (L := L) n) :=
  mono_of_mono_fac (termToReplacementQuotient_comp e hm n)

omit [∀ n, (P.obj n).IsCoherent] in
/-- The forward maps of a pro-isomorphism onto a coherent adic system are epimorphisms, even after
precomposition with a transition map. -/
theorem epi_map_comp_proIsoφ {K : ℕ} (n : ℕ) (h : e.α n ≤ K) :
    Epi (P.map (homOfLE h).op ≫ e.φ n) := by
  have hφ : ∀ j, Epi (e.φ j) := fun j => by
    have h2 := e.φψ j
    have : Epi (InverseSequence.tr N.obj (le_trans (e.αle j) (e.βle (e.α j)))) :=
      epi_map_of_isCoherentAdicSystem N.property _
    rw [← h2] at this
    exact epi_of_epi (e.ψ (e.α j)) (e.φ j)
  have hnK : n ≤ K := (e.αle n).trans h
  have h1 := e.φnat hnK
  have hN : Epi (InverseSequence.tr N.obj hnK) := epi_map_of_isCoherentAdicSystem N.property _
  have hc : Epi (e.φ K ≫ InverseSequence.tr N.obj hnK) := epi_comp' (hφ K) hN
  rw [← h1] at hc
  rw [InverseSequence.tr, map_homOfLE_op_comp P h (e.αle K), Category.assoc] at hc
  exact epi_of_epi (P.map (homOfLE (e.αle K)).op) _

variable (hk : ∀ n, e.α (e.β (L.m n)) ≤ L.k n)

include hk in
/-- The reduction `P_{k n} ⟶ P_{m n} / 𝒥 ⁿ⁺¹ P_{m n}` is the transition map `P_{k n} ⟶ P_{α n}`,
followed by the forward map `φ n : P_{α n} ⟶ N_n` of the pro-isomorphism, followed by
`termToReplacementQuotient`. -/
theorem replacementReduction_eq (n : ℕ) :
    replacementReduction J P L n =
      (P.map (homOfLE ((hm n).trans (L.m_le_k n))).op ≫ e.φ n) ≫
        termToReplacementQuotient e n := by
  have h1 := e.φnat ((L.le_m n).trans (e.βle (L.m n)))
  have h2 := e.ψφ (L.m n)
  simp only [InverseSequence.tr] at h1 h2
  rw [map_homOfLE_op_comp P (e.αmono ((L.le_m n).trans (e.βle (L.m n)))) (hk n)]
  simp only [Category.assoc]
  rw [reassoc_of% h1, termToReplacementQuotient_spec, reassoc_of% h2, ← Category.assoc,
    ← P.map_comp, replacementReduction]
  rfl

/-- The maps `N_n ⟶ P_{m n} / 𝒥 ⁿ⁺¹ P_{m n}` are compatible with the transition map `N_{n+1} ⟶ N_n`
and the map `P_{m(n+1)} / 𝒥 ⁿ⁺² P_{m(n+1)} ⟶ P_{m n} / 𝒥 ⁿ⁺¹ P_{m n}`. -/
theorem termToReplacementQuotient_drop (n : ℕ) :
    termToReplacementQuotient e (L := L) (n + 1) ≫ replacementDrop J P L n =
      N.obj.map (homOfLE (Nat.le_succ n)).op ≫ termToReplacementQuotient e n := by
  have := epi_map_of_isCoherentAdicSystem N.property
    ((L.le_m (n + 1)).trans (e.βle (L.m (n + 1))))
  rw [← cancel_epi (N.obj.map (homOfLE ((L.le_m (n + 1)).trans (e.βle (L.m (n + 1))))).op),
    ← Category.assoc, termToReplacementQuotient_spec, Category.assoc, replacementDrop]
  have h0 : cokernel.π (C := Y.Modules)
        (idealPowerMultiple J (n + 1 + 1) (P.obj (op (L.m (n + 1))))).ι ≫
      idealPowerQuotientMap J J (n + 1 + 1) (n + 1)
        (Scheme.IdealSheafData.pow_le_pow_of_le J (Nat.le_succ _))
        (P.map (homOfLE (L.mono_m (Nat.le_succ n))).op) =
      P.map (homOfLE (L.mono_m (Nat.le_succ n))).op ≫ cokernel.π (C := Y.Modules)
        (idealPowerMultiple J (n + 1) (P.obj (op (L.m n)))).ι :=
    idealPowerQuotientMap_π _ _ _ _ _ _
  rw [h0, ← Category.assoc]
  have h1 := e.ψnat (L.mono_m (Nat.le_succ n))
  simp only [InverseSequence.tr] at h1
  rw [← h1, Category.assoc, ← termToReplacementQuotient_spec, ← Category.assoc,
    ← Category.assoc, ← N.obj.map_comp, ← N.obj.map_comp]
  rfl

end Local

/-! ### Epi-mono factorizations -/

/-- Two epi-mono factorizations of the same morphism in an abelian category are isomorphic, by an
isomorphism compatible with both factorizations. -/
theorem exists_iso_of_epi_mono_fac {C : Type*} [Category C] [Abelian C] {A B I₁ I₂ : C}
    (e₁ : A ⟶ I₁) (m₁ : I₁ ⟶ B) (e₂ : A ⟶ I₂) (m₂ : I₂ ⟶ B) [Epi e₁] [Mono m₁] [Epi e₂]
    [Mono m₂] (h : e₁ ≫ m₁ = e₂ ≫ m₂) :
    ∃ i : I₁ ≅ I₂, e₁ ≫ i.hom = e₂ ∧ i.hom ≫ m₂ = m₁ := by
  have : StrongEpi e₁ := strongEpi_of_epi e₁
  have : StrongEpi e₂ := strongEpi_of_epi e₂
  have sq₁ : CommSq e₂ e₁ m₂ m₁ := ⟨h.symm⟩
  have sq₂ : CommSq e₁ e₂ m₁ m₂ := ⟨h⟩
  refine ⟨⟨sq₁.lift, sq₂.lift, ?_, ?_⟩, sq₁.fac_left, sq₁.fac_right⟩
  · rw [← cancel_epi e₁, ← Category.assoc, sq₁.fac_left, sq₂.fac_left, Category.comp_id]
  · rw [← cancel_epi e₂, ← Category.assoc, sq₂.fac_left, sq₁.fac_left, Category.comp_id]

/-! ### Restriction of the replacement to an open -/

section Restrict

variable {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData) (P : ℕᵒᵖ ⥤ X.Modules)
  [∀ n, (P.obj n).IsCoherent] (L : ReplacementLevels) (U : X.Opens)

/-- The restriction to an open `U` of every term of `P` is coherent. -/
instance isCoherent_restrict_obj (n : ℕᵒᵖ) :
    ((P ⋙ Scheme.Modules.restrictFunctor U.ι).obj n).IsCoherent :=
  @isCoherent_restrict_of_isOpenImmersion X U.toScheme U.ι _ _ (P.obj n) inferInstance

/-- The restriction of `P_{m n} / ℐ ⁿ⁺¹ P_{m n}` to `U` is the corresponding quotient of the
restriction. -/
def restrictReplacementQuotientIso (n : ℕ) :
    replacementQuotient (I.comap U.ι) (P ⋙ Scheme.Modules.restrictFunctor U.ι) L n ≅
      (Scheme.Modules.restrictFunctor U.ι).obj (replacementQuotient I P L n) :=
  haveI : (P.obj (op (L.m n))).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  restrictIdealPowerQuotientIso U.ι I (n + 1) (P.obj (op (L.m n)))

omit [AlgebraicGeometry.IsNoetherian X] in
/-- The restriction to `U` of the reduction is the reduction of the restricted system followed by
`restrictReplacementQuotientIso`. -/
theorem restrict_replacementReduction (n : ℕ) :
    (Scheme.Modules.restrictFunctor U.ι).map (replacementReduction I P L n) =
      replacementReduction (I.comap U.ι) (P ⋙ Scheme.Modules.restrictFunctor U.ι) L n ≫
        (restrictReplacementQuotientIso I P L U n).hom := by
  have : (P.obj (op (L.m n))).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  rw [replacementReduction, replacementReduction, Functor.map_comp, Category.assoc,
    restrictReplacementQuotientIso]
  exact congrArg (fun t => (Scheme.Modules.restrictFunctor U.ι).map
    (P.map (homOfLE (L.m_le_k n)).op) ≫ t)
    (cokernel_π_comp_restrictIdealPowerQuotientIso U.ι I (n + 1) (P.obj (op (L.m n)))).symm

omit [AlgebraicGeometry.IsNoetherian X] in
/-- The identifications `restrictReplacementQuotientIso` are compatible with the maps between
consecutive quotients. -/
theorem restrict_replacementDrop (n : ℕ) :
    (restrictReplacementQuotientIso I P L U (n + 1)).hom ≫
        (Scheme.Modules.restrictFunctor U.ι).map (replacementDrop I P L n) =
      replacementDrop (I.comap U.ι) (P ⋙ Scheme.Modules.restrictFunctor U.ι) L n ≫
        (restrictReplacementQuotientIso I P L U n).hom := by
  have : ∀ j, (P.obj (op j)).IsQuasicoherent := fun _ => isQuasicoherent_of_isCoherent _
  rw [← cancel_epi (cokernel.π (C := U.toScheme.Modules) (idealPowerMultiple (I.comap U.ι)
    (n + 1 + 1) ((P ⋙ Scheme.Modules.restrictFunctor U.ι).obj (op (L.m (n + 1))))).ι)]
  have h1 := cokernel_π_comp_restrictIdealPowerQuotientIso U.ι I (n + 1 + 1)
    (P.obj (op (L.m (n + 1))))
  have h2 := cokernel_π_comp_restrictIdealPowerQuotientIso U.ι I (n + 1)
    (P.obj (op (L.m n)))
  have h3 := idealPowerQuotientMap_π (I.comap U.ι) (I.comap U.ι) (n + 1 + 1) (n + 1)
    (Scheme.IdealSheafData.pow_le_pow_of_le (I.comap U.ι) (Nat.le_succ _))
    ((P ⋙ Scheme.Modules.restrictFunctor U.ι).map (homOfLE (L.mono_m (Nat.le_succ n))).op)
  have h4 := idealPowerQuotientMap_π I I (n + 1 + 1) (n + 1)
    (Scheme.IdealSheafData.pow_le_pow_of_le I (Nat.le_succ _))
    (P.map (homOfLE (L.mono_m (Nat.le_succ n))).op)
  rw [restrictReplacementQuotientIso, restrictReplacementQuotientIso]
  refine (Category.assoc (obj := U.toScheme.Modules) _ _ _).symm.trans ?_
  refine (congrArg (fun t => t ≫ (Scheme.Modules.restrictFunctor U.ι).map
    (replacementDrop I P L n)) h1).trans ?_
  refine ((Scheme.Modules.restrictFunctor U.ι).map_comp _ _).symm.trans ?_
  refine (congrArg (Scheme.Modules.restrictFunctor U.ι).map h4).trans ?_
  refine ((Scheme.Modules.restrictFunctor U.ι).map_comp _ _).trans ?_
  refine (congrArg (fun t => (Scheme.Modules.restrictFunctor U.ι).map
    (P.map (homOfLE (L.mono_m (Nat.le_succ n))).op) ≫ t) h2.symm).trans ?_
  refine (Category.assoc (obj := U.toScheme.Modules) _ _ _).symm.trans ?_
  refine (congrArg (fun t => t ≫ (restrictIdealPowerQuotientIso U.ι I (n + 1)
    (P.obj (op (L.m n)))).hom) h3.symm).trans ?_
  exact Category.assoc (obj := U.toScheme.Modules) _ _ _

variable {I P L U}

/-- A local pro-adic datum on `U`: a coherent adic system on `U` together with a pro-isomorphism
from the restriction of `P`. -/
structure LocalProAdicDatum (I : X.IdealSheafData) (P : ℕᵒᵖ ⥤ X.Modules) (U : X.Opens) where
  /-- The coherent adic system on `U`. -/
  N : CoherentAdicSystems (I.comap U.ι)
  /-- The pro-isomorphism from the restriction of `P`. -/
  e : InverseSequence.ProIso (P ⋙ Scheme.Modules.restrictFunctor U.ι) N.obj

/-- The levels `L` and the reindexing `β` are large enough for a local datum. -/
structure LocalProAdicDatum.Fits (D : LocalProAdicDatum I P U) (L : ReplacementLevels)
    (β : ℕ → ℕ) : Prop where
  /-- The quotient level dominates the forward reindexing. -/
  hm : ∀ n, D.e.α n ≤ L.m n
  /-- The source level dominates the composite reindexing at the quotient level. -/
  hk : ∀ n, D.e.α (D.e.β (L.m n)) ≤ L.k n
  /-- The global backward reindexing dominates the local one. -/
  hβ : ∀ n, D.e.β n ≤ β n
  /-- The quotient level at the backward reindexing dominates the composite reindexing. -/
  hmβ : ∀ n, D.e.α (D.e.β n) ≤ L.m (β n)

/-- For levels fitting a local datum `D` on `U`, there is an isomorphism `H_n|_U ≅ N_n` between the
restriction of the term of index `n` of the replacement and the term of the local coherent adic
system, under which the restricted projection `P_{k n}|_U ⟶ H_n|_U` becomes the transition map
`P_{k n}|_U ⟶ P_{α n}|_U` followed by the forward map `φ n` of the pro-isomorphism, and the
restricted inclusion of `H_n|_U` into the quotient becomes `termToReplacementQuotient` followed by
`restrictReplacementQuotientIso`. -/
theorem LocalProAdicDatum.exists_restrictIso (D : LocalProAdicDatum I P U) {β : ℕ → ℕ}
    (hD : D.Fits L β) (n : ℕ) :
    ∃ i : (Scheme.Modules.restrictFunctor U.ι).obj ((replacementSystem I P L).obj (op n)) ≅
        D.N.obj.obj (op n),
      (Scheme.Modules.restrictFunctor U.ι).map (replacementπ I P L n) ≫ i.hom =
        (P ⋙ Scheme.Modules.restrictFunctor U.ι).map
          (homOfLE ((hD.hm n).trans (L.m_le_k n))).op ≫ D.e.φ n ∧
      i.hom ≫ termToReplacementQuotient D.e n ≫ (restrictReplacementQuotientIso I P L U n).hom =
        (Scheme.Modules.restrictFunctor U.ι).map (replacementι I P L n) := by
  have := epi_map_comp_proIsoφ D.e n ((hD.hm n).trans (L.m_le_k n))
  have := mono_termToReplacementQuotient D.e hD.hm n
  have h := restrict_replacementReduction I P L U n
  rw [replacementReduction_eq D.e hD.hm hD.hk n, ← replacementπ_ι, Functor.map_comp,
    Category.assoc] at h
  exact exists_iso_of_epi_mono_fac _ _ _ _ h

/-- The identification of the restriction to `U` of the term of index `n` of the replacement with
the term of the local coherent adic system. -/
def LocalProAdicDatum.restrictIso (D : LocalProAdicDatum I P U) {β : ℕ → ℕ} (hD : D.Fits L β)
    (n : ℕ) :
    (Scheme.Modules.restrictFunctor U.ι).obj ((replacementSystem I P L).obj (op n)) ≅
      D.N.obj.obj (op n) :=
  (D.exists_restrictIso hD n).choose

/-- Under `LocalProAdicDatum.restrictIso`, the restricted projection `P_{k n}|_U ⟶ H_n|_U` is the
transition map `P_{k n}|_U ⟶ P_{α n}|_U` followed by the forward map `φ n` of the
pro-isomorphism. -/
theorem LocalProAdicDatum.restrictIso_π (D : LocalProAdicDatum I P U) {β : ℕ → ℕ}
    (hD : D.Fits L β) (n : ℕ) :
    (Scheme.Modules.restrictFunctor U.ι).map (replacementπ I P L n) ≫ (D.restrictIso hD n).hom =
      (P ⋙ Scheme.Modules.restrictFunctor U.ι).map
        (homOfLE ((hD.hm n).trans (L.m_le_k n))).op ≫ D.e.φ n :=
  (D.exists_restrictIso hD n).choose_spec.1

/-- The isomorphisms `LocalProAdicDatum.restrictIso` between `H_n|_U` and `N_n` are compatible with
the transition maps. -/
theorem LocalProAdicDatum.restrictIso_naturality (D : LocalProAdicDatum I P U) {β : ℕ → ℕ}
    (hD : D.Fits L β) (n : ℕ) :
    (Scheme.Modules.restrictFunctor U.ι).map
        ((replacementSystem I P L).map (homOfLE (Nat.le_succ n)).op) ≫
          (D.restrictIso hD n).hom =
      (D.restrictIso hD (n + 1)).hom ≫ D.N.obj.map (homOfLE (Nat.le_succ n)).op := by
  rw [← cancel_epi ((Scheme.Modules.restrictFunctor U.ι).map (replacementπ I P L (n + 1)))]
  have hl : (Scheme.Modules.restrictFunctor U.ι).map (replacementπ I P L (n + 1)) ≫
      (Scheme.Modules.restrictFunctor U.ι).map
        ((replacementSystem I P L).map (homOfLE (Nat.le_succ n)).op) ≫ (D.restrictIso hD n).hom =
      (P ⋙ Scheme.Modules.restrictFunctor U.ι).map
        (homOfLE (L.mono_k (Nat.le_succ n))).op ≫
      (P ⋙ Scheme.Modules.restrictFunctor U.ι).map
        (homOfLE ((hD.hm n).trans (L.m_le_k n))).op ≫ D.e.φ n := by
    rw [← Category.assoc, ← Functor.map_comp, replacementπ_map, Functor.map_comp,
      Category.assoc, D.restrictIso_π]
    rfl
  have hr : (Scheme.Modules.restrictFunctor U.ι).map (replacementπ I P L (n + 1)) ≫
      (D.restrictIso hD (n + 1)).hom ≫ D.N.obj.map (homOfLE (Nat.le_succ n)).op =
      (P ⋙ Scheme.Modules.restrictFunctor U.ι).map
        (homOfLE ((hD.hm (n + 1)).trans (L.m_le_k (n + 1)))).op ≫ D.e.φ (n + 1) ≫
          D.N.obj.map (homOfLE (Nat.le_succ n)).op := by
    rw [← Category.assoc, D.restrictIso_π, Category.assoc]
  rw [hl, hr]
  have h1 := D.e.φnat (Nat.le_succ n)
  simp only [InverseSequence.tr] at h1
  rw [← h1, ← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  rfl

variable (I P L)

omit [AlgebraicGeometry.IsNoetherian X] in
/-- The transition map `H_{n+1} ⟶ H_n` of the replacement kills `ℐ ⁿ⁺¹ H_{n+1}`. -/
theorem idealPowerMultiple_ι_comp_replacementMap (n : ℕ) :
    (idealPowerMultiple I (n + 1) ((replacementSystem I P L).obj (op (n + 1)))).ι ≫
      (replacementSystem I P L).map (homOfLE (Nat.le_succ n)).op = 0 :=
  idealPowerMultiple_ι_comp_eq_zero I _ le_rfl (idealPowerMultiple_replacementTerm_eq_bot I P L n)

/-- The map `H_{n+1} / ℐ ⁿ⁺¹ H_{n+1} ⟶ H_n` induced by the transition map of the replacement. -/
def replacementQuotientDesc (n : ℕ) :
    idealPowerQuotient I (n + 1) ((replacementSystem I P L).obj (op (n + 1))) ⟶
      (replacementSystem I P L).obj (op n) :=
  cokernel.desc _ _ (idealPowerMultiple_ι_comp_replacementMap I P L n)

variable {I P L}

/-- For levels fitting a local datum on `U`, the restriction to `U` of the comparison map
`H_{n+1} / ℐ ⁿ⁺¹ H_{n+1} ⟶ H_n` is an isomorphism. -/
theorem isIso_restrict_replacementQuotientDesc (D : LocalProAdicDatum I P U) {β : ℕ → ℕ}
    (hD : D.Fits L β) (n : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (replacementQuotientDesc I P L n)) := by
  have : ((replacementSystem I P L).obj (op (n + 1))).IsQuasicoherent :=
    have := isCoherent_replacementTerm I P L (n + 1)
    isQuasicoherent_of_isCoherent _
  obtain ⟨eN, heN⟩ := D.N.property.2.2 n
  have key : (restrictIdealPowerQuotientIso U.ι I (n + 1)
      ((replacementSystem I P L).obj (op (n + 1)))).hom ≫
        (Scheme.Modules.restrictFunctor U.ι).map (replacementQuotientDesc I P L n) =
      idealPowerQuotientMap (I.comap U.ι) (I.comap U.ι) (n + 1) (n + 1) le_rfl
        (D.restrictIso hD (n + 1)).hom ≫ eN.hom ≫ (D.restrictIso hD n).inv := by
    rw [← cancel_epi (cokernel.π (C := U.toScheme.Modules) (idealPowerMultiple (I.comap U.ι)
      (n + 1) ((Scheme.Modules.restrictFunctor U.ι).obj
        ((replacementSystem I P L).obj (op (n + 1))))).ι)]
    have h1 := cokernel_π_comp_restrictIdealPowerQuotientIso U.ι I (n + 1)
      ((replacementSystem I P L).obj (op (n + 1)))
    have h2 := idealPowerQuotientMap_π (I.comap U.ι) (I.comap U.ι) (n + 1) (n + 1) le_rfl
      (D.restrictIso hD (n + 1)).hom
    have h3 : cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1)
        ((replacementSystem I P L).obj (op (n + 1)))).ι ≫ replacementQuotientDesc I P L n =
        (replacementSystem I P L).map (homOfLE (Nat.le_succ n)).op := cokernel.π_desc _ _ _
    refine (Category.assoc (obj := U.toScheme.Modules) _ _ _).symm.trans ?_
    refine (congrArg (fun t => t ≫ (Scheme.Modules.restrictFunctor U.ι).map
      (replacementQuotientDesc I P L n)) h1).trans ?_
    refine ((Scheme.Modules.restrictFunctor U.ι).map_comp _ _).symm.trans ?_
    refine (congrArg (Scheme.Modules.restrictFunctor U.ι).map h3).trans ?_
    refine Eq.trans ?_ (Category.assoc (obj := U.toScheme.Modules) _ _ _)
    refine Eq.trans ?_ (congrArg (fun t => t ≫ eN.hom ≫ (D.restrictIso hD n).inv) h2).symm
    refine Eq.trans ?_ (Category.assoc (obj := U.toScheme.Modules) _ _ _).symm
    refine Eq.trans ?_ (congrArg (fun t => (D.restrictIso hD (n + 1)).hom ≫ t)
      (Category.assoc (obj := U.toScheme.Modules) _ _ _))
    refine Eq.trans ?_ (congrArg (fun t => (D.restrictIso hD (n + 1)).hom ≫ t ≫
      (D.restrictIso hD n).inv) heN).symm
    rw [← Category.assoc, ← D.restrictIso_naturality hD n, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hiso : IsIso ((restrictIdealPowerQuotientIso U.ι I (n + 1)
      ((replacementSystem I P L).obj (op (n + 1)))).hom ≫ (Scheme.Modules.restrictFunctor U.ι).map
      (replacementQuotientDesc I P L n)) := by
    rw [key]; infer_instance
  exact IsIso.of_isIso_comp_left (restrictIdealPowerQuotientIso U.ι I (n + 1)
      ((replacementSystem I P L).obj (op (n + 1)))).hom _

omit [AlgebraicGeometry.IsNoetherian X] in
/-- For levels fitting a local datum on `U`: if `g : T ⟶ P_{k(β j)}` is killed by the reduction at
index `β j`, then `g` followed by the transition map `P_{k(β j)} ⟶ P_j` restricts to zero on
`U`. -/
theorem LocalProAdicDatum.restrict_comp_map_eq_zero (D : LocalProAdicDatum I P U)
    {β : ℕ → ℕ} (hD : D.Fits L β) (j : ℕ) (hj : j ≤ L.k (β j)) {T : X.Modules}
    (g : T ⟶ P.obj (op (L.k (β j)))) (hg : g ≫ replacementReduction I P L (β j) = 0) :
    (Scheme.Modules.restrictFunctor U.ι).map (g ≫ P.map (homOfLE hj).op) = 0 := by
  let R := Scheme.Modules.restrictFunctor U.ι
  let Pu := P ⋙ R
  let S := idealPowerMultiple (I.comap U.ι) (β j + 1) (Pu.obj (op (L.m (β j))))
  have h0 : (R.map g ≫ Pu.map (homOfLE (L.m_le_k (β j))).op) ≫
      cokernel.π (C := U.toScheme.Modules) S.ι = 0 := by
    have h := congrArg R.map hg
    rw [R.map_comp, restrict_replacementReduction, R.map_zero] at h
    have h' := congrArg (fun t => t ≫ (restrictReplacementQuotientIso I P L U (β j)).inv) h
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, zero_comp] at h'
    rwa [Category.assoc]
  have : Mono (C := U.toScheme.Modules) S.ι := Scheme.Modules.mono_submodule_ι S
  have hk : IsLimit (KernelFork.ofι (C := U.toScheme.Modules) S.ι
      (cokernel.condition (C := U.toScheme.Modules) S.ι)) :=
    Abelian.monoIsKernelOfCokernel
      (CokernelCofork.ofπ _ (cokernel.condition (C := U.toScheme.Modules) S.ι))
      (cokernelIsCokernel (C := U.toScheme.Modules) S.ι)
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hk _ h0
  have hβj : D.e.α (D.e.β j) ≤ L.m (β j) := hD.hmβ j
  have hz : S.ι ≫ (Pu.map (homOfLE hβj).op ≫ D.e.φ (D.e.β j)) = 0 :=
    idealPowerMultiple_ι_comp_eq_zero (I.comap U.ι) _ (Nat.succ_le_succ (hD.hβ j))
      (D.N.property.2.1 _)
  have hψφ := D.e.ψφ j
  simp only [InverseSequence.tr] at hψφ
  rw [map_homOfLE_op_comp P ((D.e.βle j).trans (D.e.αle _)) (hβj.trans (L.m_le_k (β j))) hj,
    map_homOfLE_op_comp P hβj (L.m_le_k (β j)), R.map_comp]
  show R.map g ≫ Pu.map _ ≫ Pu.map _ ≫ Pu.map _ = 0
  rw [← hψφ, ← Category.assoc, ← hl]
  simp only [Category.assoc]
  have hz' : Fork.ι (KernelFork.ofι (C := U.toScheme.Modules) S.ι
      (cokernel.condition (C := U.toScheme.Modules) S.ι)) ≫ Pu.map (homOfLE hβj).op ≫
        D.e.φ (D.e.β j) ≫ D.e.ψ j = 0 :=
    (Category.assoc (obj := U.toScheme.Modules) _ _ _).symm.trans
      ((Category.assoc (obj := U.toScheme.Modules) _ _ _).symm.trans
        ((congrArg (fun t => t ≫ D.e.ψ j)
          ((Category.assoc (obj := U.toScheme.Modules) _ _ _).trans hz)).trans zero_comp))
  rw [hz', comp_zero]

end Restrict

/-! ### Pro-isomorphic coherent adic systems are isomorphic -/

section ProIsoAdic

variable {Y : Scheme.{u}} {J : Y.IdealSheafData} {A B : CoherentAdicSystems J}
  (e : InverseSequence.ProIso A.obj B.obj)

/-- For a pro-isomorphism `e` between coherent adic systems `A` and `B`, the forward map
`φ n : A_{α n} ⟶ B_n` factors through the transition map `A_{α n} ⟶ A_n`. -/
theorem exists_proIsoComponent (n : ℕ) :
    ∃ a : A.obj.obj (op n) ⟶ B.obj.obj (op n), A.obj.map (homOfLE (e.αle n)).op ≫ a = e.φ n :=
  exists_desc_of_isCoherentAdicSystem A.property _ _ (B.property.2.1 n)

/-- The component at `n` of the isomorphism attached to a pro-isomorphism. -/
def proIsoComponent (n : ℕ) : A.obj.obj (op n) ⟶ B.obj.obj (op n) :=
  (exists_proIsoComponent e n).choose

/-- The transition map `A_{α n} ⟶ A_n` followed by `proIsoComponent e n` is the forward map `φ n`
of the pro-isomorphism. -/
theorem map_proIsoComponent (n : ℕ) :
    A.obj.map (homOfLE (e.αle n)).op ≫ proIsoComponent e n = e.φ n :=
  (exists_proIsoComponent e n).choose_spec

/-- The components `A_n ⟶ B_n` attached to a pro-isomorphism are compatible with the transition
maps. -/
theorem proIsoComponent_naturality {n n' : ℕ} (h : n ≤ n') :
    A.obj.map (homOfLE h).op ≫ proIsoComponent e n =
      proIsoComponent e n' ≫ B.obj.map (homOfLE h).op := by
  have := epi_map_of_isCoherentAdicSystem A.property (e.αle n')
  rw [← cancel_epi (A.obj.map (homOfLE (e.αle n')).op), ← Category.assoc,
    ← Category.assoc, map_proIsoComponent, ← A.obj.map_comp]
  have hsplit : (homOfLE (e.αle n')).op ≫ (homOfLE h).op =
      (homOfLE (e.αmono h)).op ≫ (homOfLE (e.αle n)).op := rfl
  rw [hsplit, A.obj.map_comp, Category.assoc, map_proIsoComponent]
  exact e.φnat h

/-- The component at `n` attached to a pro-isomorphism, followed by the component at `n` attached
to its inverse, is the identity of `A_n`. -/
theorem proIsoComponent_comp_symm (n : ℕ) :
    proIsoComponent e n ≫ proIsoComponent e.symm n = 𝟙 _ := by
  have := epi_map_of_isCoherentAdicSystem A.property
    (le_trans (e.βle n) (e.αle (e.β n)))
  rw [← cancel_epi (A.obj.map (homOfLE (le_trans (e.βle n) (e.αle (e.β n)))).op),
    Category.comp_id]
  have hsplit := map_homOfLE_op_comp A.obj (e.βle n) (e.αle (e.β n))
    (le_trans (e.βle n) (e.αle (e.β n)))
  rw [hsplit, Category.assoc, reassoc_of% (proIsoComponent_naturality e (e.βle n)),
    ← Category.assoc, map_proIsoComponent]
  have h1 := map_proIsoComponent e.symm n
  change B.obj.map (homOfLE (e.βle n)).op ≫ proIsoComponent e.symm n = e.ψ n at h1
  rw [h1, e.ψφ n, ← hsplit]
  rfl

/-- A pro-isomorphism between two coherent adic systems is induced by an isomorphism. -/
def isoOfProIso : A ≅ B :=
  ObjectProperty.isoMk _
    { hom := NatTrans.ofOpSequence (proIsoComponent e) fun n =>
        proIsoComponent_naturality e (Nat.le_succ n)
      inv := NatTrans.ofOpSequence (proIsoComponent e.symm) fun n =>
        proIsoComponent_naturality e.symm (Nat.le_succ n)
      hom_inv_id := NatTrans.ext (funext fun n => proIsoComponent_comp_symm e n.unop)
      inv_hom_id := NatTrans.ext (funext fun n => proIsoComponent_comp_symm e.symm n.unop) }

/-- The transition map `A_{α n} ⟶ A_n` followed by the component at `n` of `isoOfProIso e` is the
forward map `φ n` of the pro-isomorphism. -/
theorem map_isoOfProIso_hom (n : ℕ) :
    A.obj.map (homOfLE (e.αle n)).op ≫ (isoOfProIso e).hom.hom.app (op n) = e.φ n :=
  map_proIsoComponent e n

end ProIsoAdic

/-! ### The replacement attached to a cover by local data -/

section Global

variable {X : Scheme.{u}} {I : X.IdealSheafData} {P : ℕᵒᵖ ⥤ X.Modules}
  [∀ n, (P.obj n).IsCoherent] {L : ReplacementLevels} {β : ℕ → ℕ} {ι : Type u}
  {U : ι → X.Opens} (hU : TopologicalSpace.IsOpenCover U) {D : ∀ i, LocalProAdicDatum I P (U i)}
  (hD : ∀ i, (D i).Fits L β)

omit [∀ n, (P.obj n).IsCoherent] in
include hU in
/-- Two morphisms of `𝒪_X`-modules which agree after restriction to every member of an open cover
are equal. -/
theorem hom_ext_of_isOpenCover {M N : X.Modules} (f g : M ⟶ N)
    (h : ∀ i, (Scheme.Modules.restrictFunctor (U i).ι).map f =
      (Scheme.Modules.restrictFunctor (U i).ι).map g) : f = g := by
  refine hom_ext_of_restrictCover (fun i => (U i).ι) ?_ f g h
  simp only [Scheme.Opens.ι_image_top]
  exact hU

include hU hD in
/-- The replacement is a coherent adic system. -/
theorem isCoherentAdicSystem_replacementSystem [IsNoetherian X] :
    IsCoherentAdicSystem I (replacementSystem I P L) := by
  refine ⟨fun n => isCoherent_replacementTerm I P L n,
    fun n => idealPowerMultiple_replacementTerm_eq_bot I P L n, fun n => ?_⟩
  have : IsIso (replacementQuotientDesc I P L n) :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict _ U hU
      fun i => isIso_restrict_replacementQuotientDesc (D i) (hD i) n
  exact ⟨asIso (replacementQuotientDesc I P L n), cokernel.π_desc _ _ _⟩

include hU hD in
/-- The kernel of the projection `P_{k(β j)} ⟶ H_{β j}` is killed by the transition map
`P_{k(β j)} ⟶ P_j`. -/
theorem kernel_ι_comp_map_eq_zero (j : ℕ) (hj : j ≤ L.k (β j)) :
    kernel.ι (replacementπ I P L (β j)) ≫ P.map (homOfLE hj).op = 0 := by
  refine hom_ext_of_isOpenCover hU _ _ fun i => ?_
  rw [Functor.map_zero]
  refine (D i).restrict_comp_map_eq_zero (hD i) j hj _ ?_
  rw [← replacementπ_ι, kernel.condition_assoc, zero_comp]

/-- If `n ≤ β n` for all `n`, then `j ≤ k (β j)` for all `j`. -/
theorem le_k_β (hβle : ∀ n, n ≤ β n) (j : ℕ) : j ≤ L.k (β j) :=
  (hβle j).trans ((L.le_m _).trans (L.m_le_k _))

/-- The maps back from the replacement to `P`. -/
def replacementψ (hβle : ∀ n, n ≤ β n) (j : ℕ) :
    (replacementSystem I P L).obj (op (β j)) ⟶ P.obj (op j) :=
  Abelian.epiDesc (replacementπ I P L (β j)) (P.map (homOfLE (le_k_β hβle j)).op)
    (kernel_ι_comp_map_eq_zero hU hD j (le_k_β hβle j))

/-- The projection `P_{k(β j)} ⟶ H_{β j}` followed by the map back `H_{β j} ⟶ P_j` is the
transition map `P_{k(β j)} ⟶ P_j`. -/
theorem replacementπ_ψ (hβle : ∀ n, n ≤ β n) (j : ℕ) :
    replacementπ I P L (β j) ≫ replacementψ hU hD hβle j =
      P.map (homOfLE (le_k_β hβle j)).op :=
  Abelian.comp_epiDesc _ _ _

/-- The pro-isomorphism between `P` and the replacement attached to a cover by local data. -/
def replacementProIsoOfCover (hβ : Monotone β) (hβle : ∀ n, n ≤ β n) :
    InverseSequence.ProIso P (replacementSystem I P L) :=
  replacementProIso β hβ hβle (replacementψ hU hD hβle) (replacementπ_ψ hU hD hβle)

end Global

/-! ### Maps from a coherent adic system into the replacement -/

section Lift

variable {X : Scheme.{u}} {I : X.IdealSheafData} {P : ℕᵒᵖ ⥤ X.Modules}
  [∀ n, (P.obj n).IsCoherent] (L : ReplacementLevels) (F : CoherentAdicSystems I)
  (τ : F.obj ⟶ P)

/-- There is a map `g : F_n ⟶ P_{m n} / ℐ ⁿ⁺¹ P_{m n}` whose composite with the transition map
`F_{m n} ⟶ F_n` is `τ` at level `m n` followed by the projection onto the quotient. -/
theorem exists_liftToReplacementQuotient (n : ℕ) :
    ∃ g : F.obj.obj (op n) ⟶ replacementQuotient I P L n,
      F.obj.map (homOfLE (L.le_m n)).op ≫ g = τ.app (op (L.m n)) ≫
        cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) (P.obj (op (L.m n)))).ι := by
  have : (P.obj (op (L.m n))).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  exact exists_desc_of_isCoherentAdicSystem F.property _ _
    (idealPowerMultiple_idealPowerQuotient_eq_bot I (n + 1) _)

/-- The map `F_n ⟶ P_{m n} / ℐ ⁿ⁺¹ P_{m n}` induced by `τ`. -/
def liftToReplacementQuotient (n : ℕ) : F.obj.obj (op n) ⟶ replacementQuotient I P L n :=
  (exists_liftToReplacementQuotient L F τ n).choose

/-- The transition map `F_{k n} ⟶ F_n` followed by `liftToReplacementQuotient` is `τ` at level
`k n` followed by the reduction `P_{k n} ⟶ P_{m n} / ℐ ⁿ⁺¹ P_{m n}`. -/
theorem map_liftToReplacementQuotient (n : ℕ) :
    F.obj.map (homOfLE ((L.le_m n).trans (L.m_le_k n))).op ≫
        liftToReplacementQuotient L F τ n =
      τ.app (op (L.k n)) ≫ replacementReduction I P L n := by
  rw [map_homOfLE_op_comp F.obj (L.le_m n) (L.m_le_k n), Category.assoc,
    liftToReplacementQuotient,
    (exists_liftToReplacementQuotient L F τ n).choose_spec, replacementReduction]
  have hn := τ.naturality (homOfLE (L.m_le_k n)).op
  exact (Category.assoc (obj := X.Modules) _ _ _).symm.trans
    ((congrArg (fun t => t ≫ cokernel.π (C := X.Modules)
      (idealPowerMultiple I (n + 1) (P.obj (op (L.m n)))).ι) hn).trans
      (Category.assoc (obj := X.Modules) _ _ _))

/-- The map `F_n ⟶ P_{m n} / ℐ ⁿ⁺¹ P_{m n}` induced by `τ` is killed by the cokernel of the
reduction, so it factors through the term `H_n` of the replacement. -/
theorem liftToReplacementQuotient_comp_cokernel (n : ℕ) :
    liftToReplacementQuotient L F τ n ≫ cokernel.π (replacementReduction I P L n) = 0 := by
  have := epi_map_of_isCoherentAdicSystem F.property ((L.le_m n).trans (L.m_le_k n))
  rw [← cancel_epi (F.obj.map (homOfLE ((L.le_m n).trans (L.m_le_k n))).op), comp_zero,
    ← Category.assoc, map_liftToReplacementQuotient, Category.assoc, cokernel.condition,
    comp_zero]

/-- The component at `n` of the map from `F` into the replacement. -/
def replacementLiftApp (n : ℕ) : F.obj.obj (op n) ⟶ (replacementSystem I P L).obj (op n) :=
  kernel.lift _ (liftToReplacementQuotient L F τ n)
    (liftToReplacementQuotient_comp_cokernel L F τ n)

/-- The component at `n` of the map into the replacement, followed by the inclusion of `H_n` into
`P_{m n} / ℐ ⁿ⁺¹ P_{m n}`, is `liftToReplacementQuotient`. -/
theorem replacementLiftApp_ι (n : ℕ) :
    replacementLiftApp L F τ n ≫ replacementι I P L n = liftToReplacementQuotient L F τ n :=
  kernel.lift_ι _ _ _

/-- The transition map `F_{k n} ⟶ F_n` followed by the component at `n` of the map into the
replacement is `τ` at level `k n` followed by the projection `P_{k n} ⟶ H_n`. -/
theorem map_replacementLiftApp (n : ℕ) :
    F.obj.map (homOfLE ((L.le_m n).trans (L.m_le_k n))).op ≫ replacementLiftApp L F τ n =
      τ.app (op (L.k n)) ≫ replacementπ I P L n := by
  rw [← cancel_mono (replacementι I P L n), Category.assoc, replacementLiftApp_ι,
    map_liftToReplacementQuotient, Category.assoc, replacementπ_ι]

/-- The components `F_n ⟶ H_n` of the map into the replacement are compatible with the transition
maps. -/
theorem replacementLiftApp_naturality (n : ℕ) :
    F.obj.map (homOfLE (Nat.le_succ n)).op ≫ replacementLiftApp L F τ n =
      replacementLiftApp L F τ (n + 1) ≫
        (replacementSystem I P L).map (homOfLE (Nat.le_succ n)).op := by
  have := epi_map_of_isCoherentAdicSystem F.property
    ((L.le_m (n + 1)).trans (L.m_le_k (n + 1)))
  rw [← cancel_epi (F.obj.map (homOfLE ((L.le_m (n + 1)).trans (L.m_le_k (n + 1)))).op)]
  have hr : F.obj.map (homOfLE ((L.le_m (n + 1)).trans (L.m_le_k (n + 1)))).op ≫
      replacementLiftApp L F τ (n + 1) ≫
        (replacementSystem I P L).map (homOfLE (Nat.le_succ n)).op =
      τ.app (op (L.k (n + 1))) ≫ P.map (homOfLE (L.mono_k (Nat.le_succ n))).op ≫
        replacementπ I P L n := by
    rw [← Category.assoc, map_replacementLiftApp, Category.assoc, replacementπ_map]
  rw [hr, ← Category.assoc, ← F.obj.map_comp]
  have hsplit : (homOfLE ((L.le_m (n + 1)).trans (L.m_le_k (n + 1)))).op ≫
      (homOfLE (Nat.le_succ n)).op = (homOfLE (L.mono_k (Nat.le_succ n))).op ≫
        (homOfLE ((L.le_m n).trans (L.m_le_k n))).op := rfl
  rw [hsplit, F.obj.map_comp, Category.assoc, map_replacementLiftApp, ← Category.assoc,
    τ.naturality, Category.assoc]

/-- The map from `F` into the replacement induced by `τ`. -/
def replacementLift : F.obj ⟶ replacementSystem I P L :=
  NatTrans.ofOpSequence (replacementLiftApp L F τ) (replacementLiftApp_naturality L F τ)

/-- The component at `n` of `replacementLift` is `replacementLiftApp`. -/
theorem replacementLift_app (n : ℕ) :
    (replacementLift L F τ).app (op n) = replacementLiftApp L F τ n := rfl

end Lift

/-! ### The pro-adic replacement theorem -/

section Main

variable {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)

/-- The levels attached to a finite family of local data. -/
def levelsOfFinset (t : Finset X) (a b : X → ℕ → ℕ) (ha : ∀ x, Monotone (a x))
    (hb : ∀ x, Monotone (b x)) : ReplacementLevels where
  m n := n ⊔ t.sup fun x => a x n
  k n := (n ⊔ t.sup fun x => a x n) ⊔ t.sup fun x => a x (b x (n ⊔ t.sup fun x => a x n))
  mono_m := fun i j h => sup_le_sup h (Finset.sup_mono_fun fun x _ => ha x h)
  mono_k := fun i j h => by
    have hm : (i ⊔ t.sup fun x => a x i) ≤ (j ⊔ t.sup fun x => a x j) :=
      sup_le_sup h (Finset.sup_mono_fun fun x _ => ha x h)
    exact sup_le_sup hm (Finset.sup_mono_fun fun x _ => ha x (hb x hm))
  le_m n := le_sup_left
  m_le_k n := le_sup_left

/-- **A pro-system which is locally pro-isomorphic to coherent adic systems is globally one.**
Let `X` be a Noetherian scheme, `ℐ` a quasi-coherent ideal sheaf, `(Fₙ)` an object of
`Coh(X, ℐ)`, `(Pₙ)` an inverse system of coherent `𝒪_X`-modules and `τ : (Fₙ) ⟶ (Pₙ)` a map of
inverse systems. Suppose every point of `X` has an open neighbourhood `U` on which `(Pₙ|_U)` is
pro-isomorphic to an object of `Coh(U, ℐ|_U)`. Then `(Pₙ)` is pro-isomorphic to an object
`(Hₙ)` of `Coh(X, ℐ)`, there is a morphism `σ : (Fₙ) ⟶ (Hₙ)` of `Coh(X, ℐ)` inducing `τ` up to
the pro-isomorphism, and on every open `U` the restriction of `(Hₙ)` is, compatibly with `σ`,
isomorphic to any object of `Coh(U, ℐ|_U)` to which `(Pₙ|_U)` is pro-isomorphic compatibly with
`τ`. -/
theorem exists_coherentAdicReplacement (F : CoherentAdicSystems I) (P : ℕᵒᵖ ⥤ X.Modules)
    [∀ n, (P.obj n).IsCoherent] (τ : F.obj ⟶ P)
    (hloc : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (N : CoherentAdicSystems (I.comap U.ι)),
      Nonempty (InverseSequence.ProIso (P ⋙ Scheme.Modules.restrictFunctor U.ι) N.obj)) :
    ∃ (H : CoherentAdicSystems I) (e : InverseSequence.ProIso P H.obj) (σ : F ⟶ H),
      (∀ n : ℕ, τ.app (op (e.α n)) ≫ e.φ n =
        F.obj.map (homOfLE (e.αle n)).op ≫ σ.hom.app (op n)) ∧
      (∀ (U : X.Opens) (N : CoherentAdicSystems (I.comap U.ι))
          (e' : InverseSequence.ProIso (P ⋙ Scheme.Modules.restrictFunctor U.ι) N.obj)
          (σ' : (restrictFunctor I U.ι).obj F ⟶ N),
          (∀ n : ℕ, (Functor.whiskerRight τ (Scheme.Modules.restrictFunctor U.ι)).app
              (op (e'.α n)) ≫ e'.φ n =
            ((restrictFunctor I U.ι).obj F).obj.map (homOfLE (e'.αle n)).op ≫
              σ'.hom.app (op n)) →
          ∃ i : (restrictFunctor I U.ι).obj H ≅ N, (restrictFunctor I U.ι).map σ ≫ i.hom = σ') := by
  choose U hxU N hN using hloc
  let e : ∀ x, InverseSequence.ProIso (P ⋙ Scheme.Modules.restrictFunctor (U x).ι) (N x).obj :=
    fun x => (hN x).some
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => ((U x : X.Opens) : Set X))
    (fun x => (U x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hxU x⟩)
  let L := levelsOfFinset t (fun x => (e x).α) (fun x => (e x).β) (fun x => (e x).αmono)
    (fun x => (e x).βmono)
  let β : ℕ → ℕ := fun j => j ⊔ t.sup fun x => (e x).β j
  have hβmono : Monotone β := fun i j h =>
    sup_le_sup h (Finset.sup_mono_fun fun x _ => (e x).βmono h)
  have hβle : ∀ n, n ≤ β n := fun n => le_sup_left
  let V : t → X.Opens := fun i => U i.1
  have hV : TopologicalSpace.IsOpenCover V := by
    refine top_le_iff.mp fun y _ => ?_
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hy⟩
  let D : ∀ i : t, LocalProAdicDatum I P (V i) := fun i => ⟨N i.1, e i.1⟩
  have hD : ∀ i, (D i).Fits L β := by
    rintro ⟨x, hmem⟩
    have hle : ∀ n, (e x).α n ≤ L.m n := fun n =>
      (Finset.le_sup (f := fun x => (e x).α n) hmem).trans le_sup_right
    refine ⟨hle, fun n => ?_, fun n => ?_, fun n => ?_⟩
    · exact (Finset.le_sup (f := fun x => (e x).α ((e x).β (L.m n))) hmem).trans le_sup_right
    · exact (Finset.le_sup (f := fun x => (e x).β n) hmem).trans le_sup_right
    · exact ((e x).αmono ((Finset.le_sup (f := fun x => (e x).β n) hmem).trans
        le_sup_right)).trans (hle (β n))
  let H : CoherentAdicSystems I :=
    ⟨replacementSystem I P L, isCoherentAdicSystem_replacementSystem hV hD⟩
  let E : InverseSequence.ProIso P H.obj := replacementProIsoOfCover hV hD hβmono hβle
  let σ : F ⟶ H := ObjectProperty.homMk (replacementLift L F τ)
  refine ⟨H, E, σ, fun n => (map_replacementLiftApp L F τ n).symm, ?_⟩
  intro W N' e' σ' hσ'
  let R := Scheme.Modules.restrictFunctor W.ι
  let c : InverseSequence.ProIso ((restrictFunctor I W.ι).obj H).obj N'.obj :=
    CategoryTheory.Pro.proIsoTrans (CategoryTheory.Pro.proIsoWhiskerRight E R).symm e'
  refine ⟨isoOfProIso c, ?_⟩
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun n => ?_))
  obtain ⟨n⟩ := n
  have hFU := ((restrictFunctor I W.ι).obj F).property
  let K := L.k (β (e'.α n))
  have hnK : n ≤ K := ((e'.αle n).trans (hβle _)).trans ((L.le_m _).trans (L.m_le_k _))
  have := epi_map_of_isCoherentAdicSystem hFU hnK
  rw [← cancel_epi (((restrictFunctor I W.ι).obj F).obj.map (homOfLE hnK).op)]
  have hc := map_isoOfProIso_hom c n
  change ((restrictFunctor I W.ι).obj H).obj.map (homOfLE (c.αle n)).op ≫
      (isoOfProIso c).hom.hom.app (op n) = R.map (replacementψ hV hD hβle (e'.α n)) ≫
        e'.φ n at hc
  have hσn : F.obj.map (homOfLE hnK).op ≫ (replacementLift L F τ).app (op n) =
      τ.app (op K) ≫ replacementπ I P L (β (e'.α n)) ≫
        (replacementSystem I P L).map (homOfLE ((e'.αle n).trans (hβle _))).op := by
    rw [map_homOfLE_op_comp F.obj ((e'.αle n).trans (hβle _))
      ((L.le_m _).trans (L.m_le_k _)) hnK, Category.assoc, (replacementLift L F τ).naturality,
      ← Category.assoc, replacementLift_app, map_replacementLiftApp, Category.assoc]
  have hrhs := hσ' n
  change R.map (τ.app (op (e'.α n))) ≫ e'.φ n =
    R.map (F.obj.map (homOfLE (e'.αle n)).op) ≫ σ'.hom.app (op n) at hrhs
  have hψ := replacementπ_ψ hV hD hβle (e'.α n)
  have hτ := τ.naturality (homOfLE (le_k_β (L := L) hβle (e'.α n))).op
  show R.map (F.obj.map (homOfLE hnK).op) ≫ R.map ((replacementLift L F τ).app (op n)) ≫
      (isoOfProIso c).hom.hom.app (op n) =
    R.map (F.obj.map (homOfLE hnK).op) ≫ σ'.hom.app (op n)
  have chase : ∀ {C : Type (u + 1)} [Category.{u} C] {FK Fa Fn PK Pa Hb Hn Nn : C}
      (fKn : FK ⟶ Fn) (fKa : FK ⟶ Fa) (fan : Fa ⟶ Fn) (τK : FK ⟶ PK) (τa : Fa ⟶ Pa)
      (pKa : PK ⟶ Pa) (πb : PK ⟶ Hb) (ψa : Hb ⟶ Pa) (hbn : Hb ⟶ Hn) (φn : Pa ⟶ Nn)
      (ln : Fn ⟶ Hn) (ιn : Hn ⟶ Nn) (sn : Fn ⟶ Nn), fKn = fKa ≫ fan →
      fKn ≫ ln = τK ≫ πb ≫ hbn → hbn ≫ ιn = ψa ≫ φn → πb ≫ ψa = pKa →
      fKa ≫ τa = τK ≫ pKa → τa ≫ φn = fan ≫ sn → fKn ≫ ln ≫ ιn = fKn ≫ sn := by
    intro C _ FK Fa Fn PK Pa Hb Hn Nn fKn fKa fan τK τa pKa πb ψa hbn φn ln ιn sn h0 h1 h2 h3
      h4 h5
    rw [← Category.assoc, h1, Category.assoc, Category.assoc, h2, ← Category.assoc πb, h3,
      ← Category.assoc, ← h4, Category.assoc, h5, ← Category.assoc, ← h0]
  have h1 := congrArg R.map hσn
  have hτ' := congrArg R.map hτ
  have hψ' := congrArg R.map hψ
  simp only [R.map_comp] at h1 hτ' hψ'
  exact chase _ _ _ _ _ _ _ _ _ _ _ _ _ 
    (by rw [map_homOfLE_op_comp F.obj (e'.αle n) (le_k_β (L := L) hβle (e'.α n)) hnK,
      R.map_comp]) h1 hc hψ' hτ' hrhs

/-- **Surjectivity in `Coh(X, ℐ)` is local on `X`.** A morphism of coherent adic systems whose
restriction to each member of an open covering is an epimorphism is an epimorphism. -/
theorem epi_of_epi_restrictFunctor_map {X : Scheme.{u}} [IsLocallyNoetherian X]
    {I : X.IdealSheafData} {F G : CoherentAdicSystems I} (σ : F ⟶ G) {ι : Type*}
    (U : ι → X.Opens) (hU : TopologicalSpace.IsOpenCover U)
    (h : ∀ i, Epi ((restrictFunctor I (U i).ι).map σ)) : Epi σ := by
  rw [epi_iff_epi_app_zero]
  refine Stacks.Descent.epi_of_restrictFunctor_map_epi (fun i => (U i).ι) ?_ _ fun i => ?_
  · simp only [Scheme.Opens.opensRange_ι]
    exact hU
  · exact (epi_iff_epi_app_zero (I := I.comap (U i).ι) _).mp (h i)

end Main

end Stacks.Coherent

end
