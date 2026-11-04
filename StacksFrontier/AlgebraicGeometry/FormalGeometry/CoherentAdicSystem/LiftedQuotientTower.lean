module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Assembly
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.AnnihilatedFullyFaithful

/-!
# The tower of algebraizations of the reductions of a coherent adic system

Let `X` be a Noetherian scheme, let `ℐ, 𝒦 ⊆ 𝒪_X` be quasi-coherent ideal sheaves and let `(F_n)`
be an object of `Coh(X, ℐ)`. Assume hypothesis (1) of [Stacks, Tag 088A]: completion along
`ℐ 𝒪_{X_e}` is an equivalence on `Coh(𝒪_{X_e})` for the closed subscheme `X_e = V(𝒦 ᵉ⁺¹)`, for
every `e`. The third step of the proof of Tag 088A, which this library has as
`Stacks.Coherent.exists_coherent_annihilated_completion_iso_idealPowerQuotientSystem`, then
produces for every `e` a coherent `𝒪_X`-module `G_e` annihilated by `𝒦 ᵉ⁺¹` whose completion
along `ℐ` is the reduction `(F_n / 𝒦 ᵉ⁺¹ F_n)`.

This file assembles those modules into a single object of `Coh(X, 𝒦)`. What has to be produced
is the identification

`G_{e+1} / 𝒦 ᵉ⁺¹ G_{e+1} ≅ G_e`

for every `e`, which is what `Stacks.Coherent.exists_coherentAdicSystem_of_succQuotientIso`
consumes. Completion along `ℐ` carries the left-hand side to

`(F_n / 𝒦 ᵉ⁺² F_n) / 𝒦 ᵉ⁺¹ (…) = (F_n / 𝒦 ᵉ⁺¹ F_n)`,

which is the completion of the right-hand side; and completion along `ℐ`, while not known to be
full on all of `Coh(𝒪_X)`, is fully faithful and reflects isomorphisms on the modules
annihilated by `𝒦 ᵉ⁺¹`, which is
`Stacks.Coherent.isIso_of_isIso_completion_map_of_power_annihilated`. So the identification can
be read off the completions after all.

Two comparisons of quotients are needed for the displayed computation, and are proved here:
completion commutes with reduction modulo a fixed power of a second ideal, and iterated
reduction by a smaller power collapses onto the smaller one.

## Main definitions

* `Stacks.Algebraization.idealPowerQuotientCollapseIso` — `(M / 𝒦 ˢ M) / 𝒦 ʳ (…) ≅ M / 𝒦 ʳ M`
  for `r ≤ s`.
* `Stacks.Coherent.idealPowerQuotientSystemCollapseIso` — the same for an inverse system.
* `Stacks.Coherent.completionIdealPowerQuotientSystemIso` — **completion commutes with reduction
  modulo a power of a second ideal**: `(M / 𝒦 ʳ M) ^∧_ℐ ≅ (M ^∧_ℐ) / 𝒦 ʳ (…)`.

## Main results

* `Stacks.Coherent.nonempty_idealPowerQuotient_iso_of_completion_iso` — **the successor
  identification**: two coherent modules annihilated by `𝒦 ᵉ⁺¹` whose completions are related as
  above are identified.
* `Stacks.Coherent.idealPowerMultiple_eq_bot_of_completion` — **completion reflects
  annihilation** on the `𝒦`-power-annihilated part: a coherent module annihilated by `𝒦 ᵉ⁺¹`
  whose completion is termwise annihilated by `𝒦 ⁿ⁺¹` is itself annihilated by `𝒦 ⁿ⁺¹`.

The tower itself is assembled in `FormalGeometry.GrothendieckExistenceII`, where the third step
of the proof producing the modules `G_e` lives.

## Implementation notes

The two comparisons are built with `Stacks.Algebraization.isoOfEpiFac` out of the universal
property `Stacks.Algebraization.idealPowerQuotientDesc` of the quotient projection, and are
normalized by the composite projections, which are epimorphisms
(`Stacks.Algebraization.epi_doubleIdealPowerQuotientProjection`); naturality is then forced.
The exchange of the two divisions is `Stacks.Algebraization.idealPowerQuotientCommIso`.

Indices are shifted as everywhere in this directory: the term `e` of the assembled system is the
source's `G_{e+1}`, annihilated by `𝒦 ᵉ⁺¹`.

## References

* [Stacks Project, Tag 088A](https://stacks.math.columbia.edu/tag/088A)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

variable {X : Scheme.{u}}

/-! ### Iterated reduction collapses onto the smaller power -/

section Collapse

variable (K : X.IdealSheafData) {r s : ℕ} (hrs : r ≤ s) (M : X.Modules) [M.IsQuasicoherent]

/-- The `𝒦 ˢ`-quotient of `M` maps onto the `𝒦 ʳ`-quotient when `r ≤ s`, by descending the
`𝒦 ʳ`-projection through the `𝒦 ˢ`-projection. -/
public def idealPowerQuotientDrop' : idealPowerQuotient K s M ⟶ idealPowerQuotient K r M :=
  idealPowerQuotientDesc K s (cokernel.π (C := X.Modules) (idealPowerMultiple K r M).ι)
    (idealPowerMultiple_eq_bot_of_le (idealPowerMultiple_idealPowerQuotient_eq_bot K r M) hrs)

/-- **Dividing twice by nested powers of one ideal is dividing once by the smaller.** For `r ≤ s`
and quasi-coherent `M`, the `𝒦 ʳ`-quotient of `M / 𝒦 ˢ M` is `M / 𝒦 ʳ M`. -/
public def idealPowerQuotientCollapseIso :
    idealPowerQuotient K r (idealPowerQuotient K s M) ≅ idealPowerQuotient K r M :=
  isoOfEpiFac (epi_doubleIdealPowerQuotientProjection K K r s M)
    (epi_cokernel_π_submodule_ι (idealPowerMultiple K r M))
    (idealPowerQuotientDesc K r (idealPowerQuotientDrop' K hrs M)
      (idealPowerMultiple_idealPowerQuotient_eq_bot K r M))
    (idealPowerQuotientDesc K r (doubleIdealPowerQuotientProjection K K r s M)
      (idealPowerMultiple_idealPowerQuotient_eq_bot K r (idealPowerQuotient K s M)))
    (by
      rw [doubleIdealPowerQuotientProjection, Category.assoc (obj := X.Modules),
        idealPowerQuotientDesc_π, idealPowerQuotientDrop', idealPowerQuotientDesc_π])
    (idealPowerQuotientDesc_π K r _ _)

/-- **The collapse is normalized by the composite projection.** -/
public theorem doubleIdealPowerQuotientProjection_comp_idealPowerQuotientCollapseIso :
    doubleIdealPowerQuotientProjection K K r s M ≫
        (idealPowerQuotientCollapseIso K hrs M).hom =
      cokernel.π (C := X.Modules) (idealPowerMultiple K r M).ι := by
  rw [doubleIdealPowerQuotientProjection, Category.assoc (obj := X.Modules)]
  change cokernel.π (C := X.Modules) (idealPowerMultiple K s M).ι ≫
    cokernel.π (C := X.Modules) (idealPowerMultiple K r (idealPowerQuotient K s M)).ι ≫
      idealPowerQuotientDesc K r (idealPowerQuotientDrop' K hrs M)
        (idealPowerMultiple_idealPowerQuotient_eq_bot K r M) = _
  rw [idealPowerQuotientDesc_π, idealPowerQuotientDrop', idealPowerQuotientDesc_π]

end Collapse

end Stacks.Algebraization

namespace Stacks.Coherent

variable {X : Scheme.{u}}

/-- **Iterated reduction of an inverse system collapses onto the smaller power.** -/
public def idealPowerQuotientSystemCollapseIso (K : X.IdealSheafData) {r s : ℕ} (hrs : r ≤ s)
    (F : ℕᵒᵖ ⥤ X.Modules) (hF : ∀ n : ℕᵒᵖ, (F.obj n).IsQuasicoherent) :
    idealPowerQuotientSystem K r (idealPowerQuotientSystem K s F) ≅
      idealPowerQuotientSystem K r F := by
  refine NatIso.ofComponents (fun n =>
    have := hF n
    idealPowerQuotientCollapseIso K hrs (F.obj n)) ?_
  intro m n f
  have := hF m
  have := hF n
  refine (epi_doubleIdealPowerQuotientProjection K K r s (F.obj m)).left_cancellation _ _ ?_
  have hm := doubleIdealPowerQuotientProjection_comp_idealPowerQuotientCollapseIso K hrs (F.obj m)
  have hn := doubleIdealPowerQuotientProjection_comp_idealPowerQuotientCollapseIso K hrs (F.obj n)
  have hstep : doubleIdealPowerQuotientProjection K K r s (F.obj m) ≫
      idealPowerQuotientMap K K r r le_rfl (idealPowerQuotientMap K K s s le_rfl (F.map f)) =
      F.map f ≫ doubleIdealPowerQuotientProjection K K r s (F.obj n) := by
    rw [doubleIdealPowerQuotientProjection, doubleIdealPowerQuotientProjection,
      Category.assoc (obj := X.Modules), idealPowerQuotientMap_π,
      ← Category.assoc (obj := X.Modules), idealPowerQuotientMap_π,
      Category.assoc (obj := X.Modules)]
  change doubleIdealPowerQuotientProjection K K r s (F.obj m) ≫
      idealPowerQuotientMap K K r r le_rfl (idealPowerQuotientMap K K s s le_rfl (F.map f)) ≫
        (idealPowerQuotientCollapseIso K hrs (F.obj n)).hom =
    doubleIdealPowerQuotientProjection K K r s (F.obj m) ≫
      (idealPowerQuotientCollapseIso K hrs (F.obj m)).hom ≫
        idealPowerQuotientMap K K r r le_rfl (F.map f)
  rw [← Category.assoc (obj := X.Modules), hstep, Category.assoc (obj := X.Modules), hn,
    ← Category.assoc (obj := X.Modules), hm, idealPowerQuotientMap_π]

/-! ### Completion commutes with reduction modulo a power of a second ideal -/

variable (I K : X.IdealSheafData) [IsLocallyNoetherian X]
  (M : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (r : ℕ)

/-- The `𝒦 ʳ`-quotient of a coherent module, as a coherent module. -/
public abbrev coherentIdealPowerQuotient :
    AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf :=
  ⟨idealPowerQuotient K r M.obj, isCoherent_idealPowerQuotient K r M.obj⟩

/-- The term of the comparison identifying the `n`-th term of the completion of `M / 𝒦 ʳ M` with
the `𝒦 ʳ`-quotient of the `n`-th term of the completion of `M`: both are `M` divided by
`ℐ ⁿ⁺¹ + 𝒦 ʳ`, and the identification is
`Stacks.Algebraization.idealPowerQuotientCommIso`. -/
public def completionIdealPowerQuotientTermIso (n : ℕ) :
    ((completionFunctor X I).obj (coherentIdealPowerQuotient K M r)).obj.obj (op n) ≅
      (idealPowerQuotientFunctor K r).obj
        (((completionFunctor X I).obj M).obj.obj (op n)) :=
  have : M.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent M.obj
  eqToIso (completionFunctor_obj X I (coherentIdealPowerQuotient K M r) n) ≪≫
    idealPowerQuotientCommIso I K (n + 1) r M.obj ≪≫
    ((idealPowerQuotientFunctor K r).mapIso
      (eqToIso (completionFunctor_obj X I M n))).symm

/-- **The comparison is normalized by the projections.** Composing the projection of `M` onto its
`𝒦 ʳ`-quotient with the `n`-th completion projection of that quotient and the comparison gives
the `n`-th completion projection of `M` followed by the `𝒦 ʳ`-projection. -/
public theorem completionIdealPowerQuotientTermIso_projection (n : ℕ) :
    cokernel.π (C := X.Modules) (idealPowerMultiple K r M.obj).ι ≫
        completionProjection X I (coherentIdealPowerQuotient K M r) n ≫
          (completionIdealPowerQuotientTermIso I K M r n).hom =
      completionProjection X I M n ≫ cokernel.π (C := X.Modules)
        (idealPowerMultiple K r (((completionFunctor X I).obj M).obj.obj (op n))).ι := by
  have : M.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent M.obj
  have hcancel : eqToHom
        (completionFunctor_obj X I (coherentIdealPowerQuotient K M r) n).symm ≫
      eqToHom (completionFunctor_obj X I (coherentIdealPowerQuotient K M r) n) = 𝟙 _ :=
    eqToHom_trans _ _
  have hmap := idealPowerQuotientMap_π K K r r le_rfl
    (eqToHom (completionFunctor_obj X I M n).symm)
  have hcomm := idealPowerQuotientCommMap_cokernel_π I K (n + 1) r M.obj
  change cokernel.π (C := X.Modules) (idealPowerMultiple K r M.obj).ι ≫
      (cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1)
            (coherentIdealPowerQuotient K M r).obj).ι ≫
          eqToHom (completionFunctor_obj X I (coherentIdealPowerQuotient K M r) n).symm) ≫
        eqToHom (completionFunctor_obj X I (coherentIdealPowerQuotient K M r) n) ≫
          idealPowerQuotientCommMap I K (n + 1) r M.obj ≫
            idealPowerQuotientMap K K r r le_rfl
              (eqToHom (completionFunctor_obj X I M n).symm) =
    (cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1) M.obj).ι ≫
        eqToHom (completionFunctor_obj X I M n).symm) ≫
      cokernel.π (C := X.Modules)
        (idealPowerMultiple K r (((completionFunctor X I).obj M).obj.obj (op n))).ι
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  simp only [← Category.assoc]
  simp only [Category.assoc]
  have hcomm' := idealPowerQuotientCommMap_cokernel_π_assoc I K (n + 1) r M.obj
    (idealPowerQuotientMap K K r r le_rfl
      (eqToHom (completionFunctor_obj X I M n).symm))
  exact hcomm'.trans ((congrArg (fun z => cokernel.π (C := X.Modules)
      (idealPowerMultiple I (n + 1) M.obj).ι ≫ z) hmap).trans
    (Category.assoc (obj := X.Modules) _ _ _).symm)

/-- **Completion commutes with reduction modulo a power of a second ideal.** For a coherent
`𝒪_X`-module `M`, the completion of `M / 𝒦 ʳ M` along `ℐ` is the termwise `𝒦 ʳ`-reduction of the
completion of `M`.

Each term is `Stacks.Coherent.completionIdealPowerQuotientTermIso`; naturality follows from the
normalization by the projections, which are epimorphisms. -/
public def completionIdealPowerQuotientSystemIso :
    ((completionFunctor X I).obj (coherentIdealPowerQuotient K M r)).obj ≅
      idealPowerQuotientSystem K r ((completionFunctor X I).obj M).obj := by
  have : M.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent M.obj
  refine NatIso.ofComponents
    (fun n => completionIdealPowerQuotientTermIso I K M r n.unop) ?_
  intro m n f
  have hepi : Epi (C := X.Modules) (cokernel.π (C := X.Modules)
      (idealPowerMultiple K r M.obj).ι ≫
      completionProjection X I (coherentIdealPowerQuotient K M r) m.unop) :=
    @epi_comp _ _ _ _ _ _ (epi_cokernel_π_submodule_ι _) _
      (Stacks.Algebraization.epi_completionProjection X I
        (coherentIdealPowerQuotient K M r) m.unop)
  refine hepi.left_cancellation _ _ ?_
  have hm := completionIdealPowerQuotientTermIso_projection I K M r m.unop
  have hn := completionIdealPowerQuotientTermIso_projection I K M r n.unop
  have hq := Stacks.Algebraization.completionProjection_map X I
    (coherentIdealPowerQuotient K M r) f
  have hq' := Stacks.Algebraization.completionProjection_map X I M f
  have hmapf := idealPowerQuotientMap_π K K r r le_rfl
    (((completionFunctor X I).obj M).obj.map f)
  have hleft : (cokernel.π (C := X.Modules) (idealPowerMultiple K r M.obj).ι ≫
        completionProjection X I (coherentIdealPowerQuotient K M r) m.unop) ≫
      (((completionFunctor X I).obj (coherentIdealPowerQuotient K M r)).obj.map f ≫
        (completionIdealPowerQuotientTermIso I K M r n.unop).hom) =
      completionProjection X I M n.unop ≫ cokernel.π (C := X.Modules)
        (idealPowerMultiple K r (((completionFunctor X I).obj M).obj.obj (op n.unop))).ι := by
    refine Eq.trans (Category.assoc (obj := X.Modules) _ _ _) ?_
    refine Eq.trans (congrArg (fun z => cokernel.π (C := X.Modules)
      (idealPowerMultiple K r M.obj).ι ≫ z)
        (Category.assoc (obj := X.Modules) _ _ _).symm) ?_
    refine Eq.trans (congrArg (fun z => cokernel.π (C := X.Modules)
      (idealPowerMultiple K r M.obj).ι ≫ z ≫
        (completionIdealPowerQuotientTermIso I K M r n.unop).hom) hq) ?_
    exact hn
  have hright : (cokernel.π (C := X.Modules) (idealPowerMultiple K r M.obj).ι ≫
        completionProjection X I (coherentIdealPowerQuotient K M r) m.unop) ≫
      ((completionIdealPowerQuotientTermIso I K M r m.unop).hom ≫
        (idealPowerQuotientSystem K r ((completionFunctor X I).obj M).obj).map f) =
      completionProjection X I M n.unop ≫ cokernel.π (C := X.Modules)
        (idealPowerMultiple K r (((completionFunctor X I).obj M).obj.obj (op n.unop))).ι := by
    refine Eq.trans (Category.assoc (obj := X.Modules) _ _ _) ?_
    refine Eq.trans (congrArg (fun z => cokernel.π (C := X.Modules)
      (idealPowerMultiple K r M.obj).ι ≫ z)
        (Category.assoc (obj := X.Modules) _ _ _).symm) ?_
    refine Eq.trans (Category.assoc (obj := X.Modules) _ _ _).symm ?_
    refine Eq.trans (congrArg (fun z => z ≫
      idealPowerQuotientMap K K r r le_rfl
        (((completionFunctor X I).obj M).obj.map f)) hm) ?_
    refine Eq.trans (Category.assoc (obj := X.Modules) _ _ _) ?_
    refine Eq.trans (congrArg (fun z => completionProjection X I M m.unop ≫ z) hmapf) ?_
    refine Eq.trans (Category.assoc (obj := X.Modules) _ _ _).symm ?_
    exact congrArg (fun z => z ≫ cokernel.π (C := X.Modules)
      (idealPowerMultiple K r (((completionFunctor X I).obj M).obj.obj (op n.unop))).ι) hq'
  exact hleft.trans hright.symm

/-! ### The successor identification -/

omit [IsLocallyNoetherian X] in
/-- **The successor identification of the proof of [Stacks, Tag 088A].** Let `A` be a coherent
`𝒪_X`-module annihilated by `𝒦 ᵉ⁺²`, let `B` be one annihilated by `𝒦 ᵉ⁺¹`, and suppose the
`ℐ`-completion of `A / 𝒦 ᵉ⁺¹ A` is isomorphic to that of `B`. Granted hypothesis (1) of Tag 088A
at the level `e`, the two modules themselves are isomorphic:

`A / 𝒦 ᵉ⁺¹ A ≅ B`.

Both sides are annihilated by `𝒦 ᵉ⁺¹`, so completion along `ℐ` is fully faithful on them by
`Stacks.Coherent.exists_unique_completion_preimage_of_power_annihilated`; the given isomorphism
of completions therefore comes from a morphism and from one in the other direction, and the two
composites are identities because completion is faithful there. -/
public theorem nonempty_idealPowerQuotient_iso_of_completion_iso [IsLocallyNoetherian X]
    (I K : X.IdealSheafData) (e : ℕ)
    (h : letI : IsLocallyNoetherian (K ^ (e + 1)).subscheme :=
        isLocallyNoetherian_of_isClosedImmersion (K ^ (e + 1)).subschemeι
      (completionFunctor (K ^ (e + 1)).subscheme
        (I.comap (K ^ (e + 1)).subschemeι)).IsEquivalence)
    (A B : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hB : idealPowerMultiple K (e + 1) B.obj = ⊥)
    (d : ((completionFunctor X I).obj (coherentIdealPowerQuotient K A (e + 1))).obj ≅
      ((completionFunctor X I).obj B).obj) :
    Nonempty (idealPowerQuotient K (e + 1) A.obj ≅ B.obj) := by
  have : A.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent A.obj
  have hQ : idealPowerMultiple K (e + 1) (coherentIdealPowerQuotient K A (e + 1)).obj = ⊥ :=
    idealPowerMultiple_idealPowerQuotient_eq_bot K (e + 1) A.obj
  obtain ⟨psi, hpsi, -⟩ := exists_unique_completion_preimage_of_power_annihilated I K e h
    (coherentIdealPowerQuotient K A (e + 1)) B hQ hB
    (ObjectProperty.isoMk (IsCoherentAdicSystem I) d).hom
  obtain ⟨chi, hchi, -⟩ := exists_unique_completion_preimage_of_power_annihilated I K e h
    B (coherentIdealPowerQuotient K A (e + 1)) hB hQ
    (ObjectProperty.isoMk (IsCoherentAdicSystem I) d).inv
  refine ⟨(ObjectProperty.ι _).mapIso ⟨psi, chi, ?_, ?_⟩⟩
  · refine completion_map_injective_of_power_annihilated I K e h hQ hQ ?_
    rw [(completionFunctor X I).map_comp, hpsi, hchi, Iso.hom_inv_id,
      (completionFunctor X I).map_id]
  · refine completion_map_injective_of_power_annihilated I K e h hB hB ?_
    rw [(completionFunctor X I).map_comp, hchi, hpsi, Iso.inv_hom_id,
      (completionFunctor X I).map_id]

/-! ### Completion reflects annihilation -/

omit [IsLocallyNoetherian X] in
/-- **Completion reflects annihilation on the `𝒦`-power-annihilated part.** Let `M` be a
coherent `𝒪_X`-module annihilated by `𝒦 ᵉ⁺¹`, and suppose hypothesis (1) of [Stacks, Tag 088A]
holds at the level `e`. If every term of the `ℐ`-completion of `M` is annihilated by `𝒦 ⁿ⁺¹`,
then so is `M` itself.

The projection `q : M ⟶ M / 𝒦 ⁿ⁺¹ M` has invertible completion, because completion commutes
with reduction modulo `𝒦 ⁿ⁺¹` and that reduction is invertible on each term of the completion by
hypothesis. Both `M` and `M / 𝒦 ⁿ⁺¹ M` are annihilated by `𝒦 ᵉ⁺¹`, so completion reflects
isomorphisms between them and `q` is invertible; a quotient projection which is invertible is a
monomorphism, and the subsheaf it kills is therefore zero.

This is what carries annihilation of the levelwise kernels and cokernels of a comparison map
back from the completions, which is the step of the proof of Tag 088A that makes the comparison
`(G_e) ⟶ H ^∧` along `𝒦` usable. -/
public theorem idealPowerMultiple_eq_bot_of_completion [IsLocallyNoetherian X]
    (I K : X.IdealSheafData) (e n : ℕ)
    (h : letI : IsLocallyNoetherian (K ^ (e + 1)).subscheme :=
        isLocallyNoetherian_of_isClosedImmersion (K ^ (e + 1)).subschemeι
      (completionFunctor (K ^ (e + 1)).subscheme
        (I.comap (K ^ (e + 1)).subschemeι)).IsEquivalence)
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hM : idealPowerMultiple K (e + 1) M.obj = ⊥)
    (hC : ∀ k : ℕ, idealPowerMultiple K (n + 1)
      (((completionFunctor X I).obj M).obj.obj (op k)) = ⊥) :
    idealPowerMultiple K (n + 1) M.obj = ⊥ := by
  have : M.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent M.obj
  let q : M ⟶ coherentIdealPowerQuotient K M (n + 1) :=
    ObjectProperty.homMk
      (cokernel.π (C := X.Modules) (idealPowerMultiple K (n + 1) M.obj).ι)
  have hQ : idealPowerMultiple K (e + 1)
      (coherentIdealPowerQuotient K M (n + 1)).obj = ⊥ :=
    idealPowerMultiple_idealPowerQuotient_eq_bot_of_eq_bot K K (e + 1) (n + 1) M.obj hM
  have happ : ∀ k : ℕᵒᵖ, IsIso (((completionFunctor X I).map q).hom.app k) := by
    intro k
    have hiso : IsIso (cokernel.π (C := X.Modules) (idealPowerMultiple K (n + 1)
        (((completionFunctor X I).obj M).obj.obj (op k.unop))).ι) :=
      isIso_cokernel_π_of_idealPowerMultiple_eq_bot K (n + 1) _ (hC k.unop)
    have hkey : ((completionFunctor X I).map q).hom.app (op k.unop) ≫
        (completionIdealPowerQuotientTermIso I K M (n + 1) k.unop).hom =
        cokernel.π (C := X.Modules) (idealPowerMultiple K (n + 1)
          (((completionFunctor X I).obj M).obj.obj (op k.unop))).ι := by
      refine (Stacks.Algebraization.epi_completionProjection X I M k.unop).left_cancellation
        _ _ ?_
      refine Eq.trans (Category.assoc (obj := X.Modules) _ _ _).symm ?_
      refine Eq.trans (congrArg (fun z => z ≫
        (completionIdealPowerQuotientTermIso I K M (n + 1) k.unop).hom)
          (completionFunctor_map_quotient X I q k.unop)) ?_
      refine Eq.trans (Category.assoc (obj := X.Modules) _ _ _) ?_
      exact completionIdealPowerQuotientTermIso_projection I K M (n + 1) k.unop
    have : IsIso (((completionFunctor X I).map q).hom.app (op k.unop) ≫
        (completionIdealPowerQuotientTermIso I K M (n + 1) k.unop).hom) := hkey ▸ hiso
    exact IsIso.of_isIso_comp_right _
      (completionIdealPowerQuotientTermIso I K M (n + 1) k.unop).hom
  have : ∀ k : ℕᵒᵖ, IsIso (((completionFunctor X I).map q).hom.app k) := happ
  have hnat : IsIso ((completionFunctor X I).map q).hom := NatIso.isIso_of_isIso_app _
  have : IsIso ((ObjectProperty.ι (IsCoherentAdicSystem I)).map
    ((completionFunctor X I).map q)) := hnat
  have : IsIso ((completionFunctor X I).map q) :=
    isIso_of_reflects_iso ((completionFunctor X I).map q)
      (ObjectProperty.ι (IsCoherentAdicSystem I))
  have : IsIso q := isIso_of_isIso_completion_map_of_power_annihilated I K e h hM hQ q
  have hsplit : (ObjectProperty.ι _).map q ≫
      (ObjectProperty.ι _).map (inv q) = 𝟙 M.obj :=
    ((ObjectProperty.ι _).map_comp q (inv q)).symm.trans
      ((congrArg (ObjectProperty.ι _).map
        (IsIso.hom_inv_id q)).trans
        ((ObjectProperty.ι _).map_id M))
  have : Mono (C := X.Modules)
      (cokernel.π (C := X.Modules) (idealPowerMultiple K (n + 1) M.obj).ι) :=
    SplitMono.mono ⟨(ObjectProperty.ι _).map (inv q), hsplit⟩
  refine (submodule_ι_eq_zero_iff _).1 ?_
  refine (cancel_mono (cokernel.π (C := X.Modules)
    (idealPowerMultiple K (n + 1) M.obj).ι)).1 ?_
  exact (cokernel.condition (C := X.Modules) _).trans (zero_comp (C := X.Modules)).symm

end Stacks.Coherent

end
