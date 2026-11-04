module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KoszulStalkComplexIso
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulAugmentation
public import StacksFrontier.Topology.Sheaves.Modules.Exactness

/-!
# Koszul-regularity of the germs makes the Koszul complex of sheaves a resolution

Let `O♯` be a sheaf of commutative rings on a topological space `X`, let `f₁, …, f_r` be global
sections of `O♯` and let `φ : (O♯)ʳ ⟶ O♯` be the morphism of sheaves of modules they define.
The Koszul complex of `φ` is a complex of sheaves of `O♯`-modules, and its stalk at a point `x`
is the ring-level Koszul complex of the germs `f_{1,x}, …, f_{r,x}` in `O♯_x`. Since exactness of
a complex of sheaves is exactness of all of its complexes of stalks, the Koszul complex of
sheaves is acyclic in a degree exactly when every ring-level Koszul complex of germs is.

Together with the unconditional computation of `H₀` this discharges the hypothesis of
`Stacks.RegularSequence.KoszulChainData.quasiIso_augmentation`: if every sequence of germs is
Koszul-regular in the sense of `Koszul.IsKoszulRegular`, then the augmentation

`K_•(O♯, f₁, …, f_r) ⟶ (O♯/I)[0]`

is a quasi-isomorphism, that is, the Koszul complex is a resolution of `O♯/I` by sheaves of
modules whose terms are exterior powers of `(O♯)ʳ`.

## Main results

* `Stacks.RegularSequence.exactAt_iff_forall_stalkAbFunctor_exactAt`: exactness of a complex of
  sheaves of modules in one degree, tested on the complexes of stalks of abelian groups, in an
  arbitrary complex shape.
* `Stacks.RegularSequence.KoszulChainData.exactAt_chain_natCast_iff` and
  `Stacks.RegularSequence.KoszulChainData.isZero_homology_chain_natCast_iff`: **the Koszul
  complex of sheaves is exact in degree `n` exactly when the ring-level Koszul complex of the
  germs is, at every point.**
* `Stacks.RegularSequence.KoszulChainData.isZero_homology_chain_of_neg`: the Koszul complex of
  sheaves is acyclic in negative degrees, where it vanishes.
* `Stacks.RegularSequence.KoszulChainData.quasiIso_augmentation_of_forall_germ_isKoszulRegular`
  and `Stacks.RegularSequence.quasiIso_koszulAugmentation_of_forall_germ_isKoszulRegular`:
  **Koszul-regularity of every sequence of germs makes the augmentation a quasi-isomorphism.**

## Implementation notes

The stalk comparison used is `Stacks.RegularSequence.KoszulChainData.stalkChainIso`, which is
already stated in the `ℤ`-indexed, abelian-group-valued form: the ring-level Koszul complex,
which is indexed by `ℕ`, is extended by zero to negative degrees and re-indexed over `ℤ`, and
the module structure over the stalk ring is forgotten. Exactness crosses both of those steps
by `Stacks.ChainComplexIntBridge.natToIntAb_exactAt_iff`, so the only new ingredient here is
the passage from exactness of a complex of sheaves to exactness of its complexes of stalks.

That passage is `AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact` applied to
the `n`-th short complex. No transport is needed: the `n`-th short complex of the complex of
stalks is literally the image under the stalk functor of the `n`-th short complex of the
original, so the two readings of the statement are definitionally equal. The complex shape is
left arbitrary, since the Koszul complex is a chain complex over `ℤ` while the statements of
`StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic` are about cochain complexes.

The degree hypothesis is split by sign. In negative degrees the Koszul complex vanishes, so its
homology does, with no hypothesis at all; in positive degrees the degree is a natural number and
the stalkwise criterion applies. Degree zero is the one degree the hypothesis says nothing
about, and it is the degree the augmentation handles.

## References

* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
* [Stacks Project, Tag 062E](https://stacks.math.columbia.edu/tag/062E)
* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
* [Stacks Project, Tag 063C](https://stacks.math.columbia.edu/tag/063C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace

universe u

namespace Stacks.RegularSequence

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}

/-- **Exactness of a complex of sheaves of modules is a stalkwise condition.** A complex of
sheaves of `O♯`-modules, in any complex shape, is exact in a degree exactly when the complex of
stalks of the underlying presheaves of abelian groups is exact in that degree at every point.

This is `AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact` read on the short
complex cut out in that degree. -/
theorem exactAt_iff_forall_stalkAbFunctor_exactAt {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex
      (SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)) c) (i : ι) :
    K.ExactAt i ↔ ∀ x : ↥X,
      (((stalkAbFunctor Osharp x).mapHomologicalComplex c).obj K).ExactAt i := by
  rw [HomologicalComplex.exactAt_iff,
    AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact]
  exact Iff.rfl

variable {r : ℕ}
  {A : SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X)
    (koszulFreeSheaf Osharp r)}
  {φ : koszulFreeSheaf Osharp r ⟶
    SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

namespace KoszulChainData

variable (K : KoszulChainData.{u, u, u} A φ)
  (f : Fin r → ↑(Osharp.obj.obj (op (⊤ : Opens ↥X))))
  (hφ : ∀ k : Fin r,
    ((SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Osharp)).freeHomEquiv φ
      (ULift.up k)).val (op (⊤ : Opens ↥X)) = f k)

include hφ in
/-- **The Koszul complex of sheaves is exact in degree `n` exactly when all the ring-level
Koszul complexes of germs are.** The stalk at `x` of the Koszul complex of `φ` is the Koszul
complex of the germs of `f` at `x`, extended by zero to negative degrees, and exactness of a
complex of sheaves is exactness of all of its complexes of stalks. -/
theorem exactAt_chain_natCast_iff (n : ℕ) :
    K.chain.ExactAt (n : ℤ) ↔ ∀ x : ↥X,
      (Koszul.seqComplex fun k =>
        TopCat.Presheaf.germ Osharp.obj (⊤ : Opens ↥X) x (Opens.mem_top x) (f k)).ExactAt n := by
  rw [exactAt_iff_forall_stalkAbFunctor_exactAt]
  refine forall_congr' fun x => ?_
  rw [ChainComplexIntBridge.exactAt_iff_of_iso (K.stalkChainIso f hφ x) (n : ℤ)]
  exact ChainComplexIntBridge.natToIntAb_exactAt_iff _ n

include hφ in
/-- **The homology of the Koszul complex of sheaves vanishes in degree `n` exactly when the
homology of all the ring-level Koszul complexes of germs does.** -/
theorem isZero_homology_chain_natCast_iff (n : ℕ) :
    IsZero (K.chain.homology (n : ℤ)) ↔ ∀ x : ↥X,
      IsZero ((Koszul.seqComplex fun k =>
        TopCat.Presheaf.germ Osharp.obj (⊤ : Opens ↥X) x (Opens.mem_top x) (f k)).homology n) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology, K.exactAt_chain_natCast_iff f hφ n]
  exact forall_congr' fun _ => HomologicalComplex.exactAt_iff_isZero_homology _ _

/-- **The Koszul complex of sheaves is acyclic in negative degrees**, where it vanishes. -/
theorem isZero_homology_chain_of_neg (n : ℤ) (hn : n < 0) : IsZero (K.chain.homology n) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _ (K.isZero_chain_X_of_neg hn)

include hφ in
/-- **Koszul-regularity of every sequence of germs makes the Koszul complex of sheaves acyclic
outside degree zero.** In negative degrees the complex vanishes; in positive degrees the degree
is a natural number and the stalkwise criterion turns the hypothesis into the required
vanishing. -/
theorem isZero_homology_chain_of_forall_germ_isKoszulRegular
    (h : ∀ x : ↥X, Koszul.IsKoszulRegular fun k =>
      TopCat.Presheaf.germ Osharp.obj (⊤ : Opens ↥X) x (Opens.mem_top x) (f k))
    (n : ℤ) (hn : n ≠ 0) : IsZero (K.chain.homology n) := by
  rcases lt_trichotomy n 0 with hneg | rfl | hpos
  · exact K.isZero_homology_chain_of_neg n hneg
  · exact absurd rfl hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hpos.le
    exact (K.isZero_homology_chain_natCast_iff f hφ m).2 fun x => h x m (by omega)

include hφ in
/-- **The Koszul complex of a sequence of global sections whose germs are everywhere
Koszul-regular is a resolution of `O♯/I`.** The augmentation is a quasi-isomorphism: in degree
zero because `H₀` of the Koszul complex is the quotient unconditionally, and in every other
degree because both sides vanish. -/
theorem quasiIso_augmentation_of_forall_germ_isKoszulRegular
    (h : ∀ x : ↥X, Koszul.IsKoszulRegular fun k =>
      TopCat.Presheaf.germ Osharp.obj (⊤ : Opens ↥X) x (Opens.mem_top x) (f k)) :
    QuasiIso K.augmentation :=
  K.quasiIso_augmentation (K.isZero_homology_chain_of_forall_germ_isKoszulRegular f hφ h)

end KoszulChainData

/-- **The Koszul complex of `φ` on the constructed algebra bundle is a resolution of `O♯/I`
when the germs of the sequence are everywhere Koszul-regular.** -/
theorem quasiIso_koszulAugmentation_of_forall_germ_isKoszulRegular
    (φ : koszulFreeSheaf Osharp r ⟶
      SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Osharp))
    (f : Fin r → ↑(Osharp.obj.obj (op (⊤ : Opens ↥X))))
    (hφ : ∀ k : Fin r,
      ((SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Osharp)).freeHomEquiv φ
        (ULift.up k)).val (op (⊤ : Opens ↥X)) = f k)
    (h : ∀ x : ↥X, Koszul.IsKoszulRegular fun k =>
      TopCat.Presheaf.germ Osharp.obj (⊤ : Opens ↥X) x (Opens.mem_top x) (f k)) :
    QuasiIso (koszulAugmentation φ) :=
  (koszulChainData φ).quasiIso_augmentation_of_forall_germ_isKoszulRegular f hφ h

end Stacks.RegularSequence

end
