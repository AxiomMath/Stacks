module

public import StacksFrontier.AlgebraicGeometry.AffineVanishingUnbounded.Tower
public import StacksFrontier.AlgebraicGeometry.Cohomology.TruncationTowerAnyModel
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyLimit
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre

/-!
# From the truncation tower to the unbounded affine vanishing comparison

`StacksFrontier/AlgebraicGeometry/AffineVanishingUnbounded/Tower.lean` runs the
`E = R\lim \tau_{\geq -n}E` argument of [Stacks, Tag 08D4] over an affine base and reduces the
invertibility of the comparison
$$ Q(\Gamma(\operatorname{Spec} R, \widetilde{M}^\bullet)) \longrightarrow R\Gamma(E),
   \qquad E = Q(\widetilde{M}^\bullet), $$
to the geometric input that `E` *is* the derived limit of the tower of its truncations. It takes
that input in the shape [Stacks, Tag 070F] and [Stacks, Tag 070M] deliver it — a tower `𝓘` of
bounded below complexes with `Γ`-acyclic terms, quasi-isomorphisms from the sheafified algebraic
truncations onto its terms, *and a presented derived-limit triangle for `𝓘 ⋙ Q` whose cone is the
canonical one*.

`StacksFrontier/AlgebraicGeometry/Cohomology/TruncationTowerAnyModel.lean` proves
[Stacks, Tag 08D3] — but about `truncGETower`, the tower `n ↦ \tau_{\geq -n}E` inside the derived
category, and in the form *every presented derived limit of that tower receives an isomorphism
from `E`*. This file closes the gap between the two shapes, in two steps.

1. **Tag 08D3 in canonical form.** Products in `D(\mathcal{O}_X)` exist, so the truncation tower
   has *some* derived limit; the canonical cone `(\pi_{\tau_{\geq -n}})_n : E \to \prod
   \tau_{\geq -n}E` kills the Milnor difference map, because
   `TStructure.π_natTransTruncGEOfLE_app` says the truncation maps are compatible with the
   transitions, so it factors through that limit; Tag 08D3 makes the factorization invertible;
   and transporting the triangle along it exhibits **`E` itself** as a derived limit of
   `truncGETower`, with the canonical truncation maps as its projections. That is
   `Stacks.TruncationTower.exists_isDerivedLimit_truncGETower_of_isQuasicoherent`.
2. **Transport along an isomorphism of towers.** A presented derived-limit triangle for one
   `ℕᵒᵖ`-tower transports to any objectwise-isomorphic one whose isomorphisms commute with the
   successor transitions, the product comparison being carried by `HasLimit.isoOfNatIso`, and the
   normalization of the cone transports with it. That is
   `Stacks.DerivedLimit.exists_distTriang_of_towerIso`, and the proof is the product-comparison
   transport of
   `Stacks.TruncationTower.isIso_to_isDerivedLimit_truncGETower` with the comparison functor
   replaced by the identity and the tower isomorphism no longer required to be natural.

Composing the two discharges the derived-limit hypothesis of
`StacksFrontier/AlgebraicGeometry/AffineVanishingUnbounded/Tower.lean` outright. What is left of
the geometric input is purely local: a tower `𝓘` of `Γ`-acyclic resolutions of the sheafified
truncations (hypotheses `𝓘`, `hGE`, `hac`, `g`, `hg`), isomorphisms `ι` identifying `Q(𝓘_n)`
with `\tau_{\geq -n}E` under the canonical maps (`hι`), and the compatibility of the resolutions
with the transitions of the tower (`hnat`). No statement about derived limits, countable products
or Mittag-Leffler systems remains among the hypotheses.

## Main results

* `Stacks.DerivedLimit.exists_distTriang_of_towerIso` — a presented derived limit of an
  `ℕᵒᵖ`-tower in a pre-triangulated category transports along objectwise isomorphisms commuting
  with the successor transitions, carrying the normalization of its cone with it.
* `Stacks.TruncationTower.isQuasicoherent_homologyFunctor_Q_obj` — the cohomology of the object of
  `D(\mathcal{O}_X)` represented by a complex of quasi-coherent modules is quasi-coherent.
* `Stacks.TruncationTower.exists_isDerivedLimit_truncGETower_of_isQuasicoherent` —
  **[Stacks, Tag 08D3] in canonical form**: an object of `D(\mathcal{O}_X)` with quasi-coherent
  cohomology is a derived limit of the tower of its truncations from below, with the canonical
  truncation maps as the projections of the cone.
* `AlgebraicGeometry.isIso_globalSectionsComplexComparison_tilde_of_resolutionTower` —
  **unbounded affine vanishing from a resolution tower alone**: the comparison
  `Q(\Gamma(\operatorname{Spec} R, \widetilde{M}^\bullet)) \to R\Gamma(Q(\widetilde{M}^\bullet))`
  is invertible as soon as there is a tower of `Γ`-acyclic resolutions of the sheafified
  truncations of `M^\bullet` computing the truncations of `Q(\widetilde{M}^\bullet)`.

## Implementation notes

*Why the transport lemma takes objectwise isomorphisms rather than a natural isomorphism of
functors.* The tower it is applied to is `truncGETower`, built by
`CategoryTheory.Functor.ofOpSequence`, and the data available on the geometric side is one
isomorphism per natural number together with one square per successor. Promoting that to a
natural isomorphism of functors `ℕᵒᵖ ⥤ D` would require naturality for every `≤`, which is an
induction with nothing to gain: the product comparison and the Milnor difference map involve only
the successor transitions.

*Why three steps are in term mode.* `rw` builds its motive at `implicit` transparency, and
`(truncGETower A E).obj ⟨n⟩` is only semireducibly `(TStructure.t.truncGE (-n)).obj E`. So
`rw [← Category.assoc]` fails on goals whose middle object is written the first way, with the
misleading message that the pattern `?f ≫ ?g ≫ ?h` does not occur in a goal that visibly
contains it; the successor square in the last proof is therefore assembled from `congrArg`,
`Eq.trans` and `Category.assoc` as terms. For the same reason the canonical cone of the second
result is obtained as an existential — `Pi.lift` of the truncation maps, together with its
projection formula — rather than written into the proof, so that no rewrite ever has to abstract
over the mismatched spelling.

*Quasi-coherence of cohomology.* The quasi-coherent modules are a weak Serre class
(`Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerreClass`), hence closed
under kernels and cokernels, and the cohomology of a complex is a cokernel of a map into a
kernel; `DerivedCategory.homologyFunctorFactors` transfers that to the derived category.

## References

* [Stacks Project, Tag 08D3](https://stacks.math.columbia.edu/tag/08D3)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 08TC](https://stacks.math.columbia.edu/tag/08TC)
* [Stacks Project, Tag 070F](https://stacks.math.columbia.edu/tag/070F)
* [Stacks Project, Tag 070M](https://stacks.math.columbia.edu/tag/070M)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated AlgebraicGeometry DerivedCategory
open Stacks.DerivedLimit

universe v u

namespace Stacks.DerivedLimit

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **A presented derived limit transports along an isomorphism of towers.** Let `F` and `G` be
`ℕᵒᵖ`-indexed towers in a pre-triangulated category whose terms have products, and let
`ι n : F_n ≅ G_n` be isomorphisms commuting with the successor transitions. If `E` sits in a
distinguished triangle exhibiting it as the derived limit of `F`, with cone `u`, then it sits in
one exhibiting it as the derived limit of `G`, with cone `ι ∘ u`.

The isomorphisms assemble into `HasLimit.isoOfNatIso` between the two products; that isomorphism
intertwines the two Milnor difference maps, because the squares commute, and the triangle is
transported along it. -/
theorem exists_distTriang_of_towerIso
    {F G : ℕᵒᵖ ⥤ D}
    [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩] [HasProduct fun n : ℕ ↦ G.obj ⟨n⟩]
    (ι : ∀ n : ℕ, F.obj ⟨n⟩ ≅ G.obj ⟨n⟩)
    (hsq : ∀ n : ℕ, (ι (n + 1)).hom ≫ G.map (homOfLE (Nat.le_succ n)).op =
      F.map (homOfLE (Nat.le_succ n)).op ≫ (ι n).hom)
    {E : D} {u : ∀ n : ℕ, E ⟶ F.obj ⟨n⟩}
    (p : E ⟶ ∏ᶜ fun n : ℕ ↦ F.obj ⟨n⟩)
    (δ : (∏ᶜ fun n : ℕ ↦ F.obj ⟨n⟩) ⟶ E⟦(1 : ℤ)⟧)
    (hT : Triangle.mk p (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op) δ ∈
      distTriang D)
    (hp : ∀ n : ℕ, p ≫ Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n = u n) :
    ∃ (p' : E ⟶ ∏ᶜ fun n : ℕ ↦ G.obj ⟨n⟩)
      (δ' : (∏ᶜ fun n : ℕ ↦ G.obj ⟨n⟩) ⟶ E⟦(1 : ℤ)⟧),
      Triangle.mk p' (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ G.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ G.obj ⟨n⟩) (n + 1) ≫ G.map (homOfLE (Nat.le_succ n)).op) δ' ∈
        distTriang D ∧
        ∀ n : ℕ, p' ≫ Pi.π (fun n : ℕ ↦ G.obj ⟨n⟩) n = u n ≫ (ι n).hom := by
  let e : Discrete.functor (fun n : ℕ ↦ F.obj ⟨n⟩) ≅ Discrete.functor (fun n : ℕ ↦ G.obj ⟨n⟩) :=
    Discrete.natIso fun j ↦ ι j.as
  let pIso : (∏ᶜ fun n : ℕ ↦ F.obj ⟨n⟩) ≅ ∏ᶜ fun n : ℕ ↦ G.obj ⟨n⟩ := HasLimit.isoOfNatIso e
  have hpi : ∀ n : ℕ, pIso.hom ≫ Pi.π (fun n : ℕ ↦ G.obj ⟨n⟩) n =
      Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n ≫ (ι n).hom := fun n ↦
    HasLimit.isoOfNatIso_hom_π e ⟨n⟩
  have hcomm : pIso.hom ≫ (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ G.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ G.obj ⟨n⟩) (n + 1) ≫ G.map (homOfLE (Nat.le_succ n)).op) =
      (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op) ≫
        pIso.hom := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    conv_rhs => rw [Category.assoc, hpi n, ← Category.assoc, Pi.lift_comp_π, Preadditive.sub_comp,
      Category.assoc]
    simp only [Category.assoc, Pi.lift_comp_π, Preadditive.comp_sub, hpi, reassoc_of% hpi, hsq]
  refine ⟨p ≫ pIso.hom, pIso.inv ≫ δ, ?_, ?_⟩
  · refine isomorphic_distinguished _ hT _ ?_
    refine Triangle.isoMk _ _ (Iso.refl E) pIso.symm pIso.symm ?_ ?_ ?_
    · simp
    · dsimp only [Triangle.mk_mor₂, Iso.symm_hom]
      rw [Iso.eq_inv_comp, ← Category.assoc, hcomm, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    · simp
  · intro n
    rw [Category.assoc, hpi n, ← Category.assoc, hp n]

end Stacks.DerivedLimit

namespace Stacks.TruncationTower

/-- **The cohomology of a complex of quasi-coherent modules is quasi-coherent.** If every term of
a cochain complex `K` of `𝒪_X`-modules on a scheme `X` is quasi-coherent, then so is
`Hⁿ(Q(K))`.

The quasi-coherent modules are closed under kernels and cokernels, being a weak Serre class, and
`Hⁿ(K)` is a cokernel of a map into a kernel; `DerivedCategory.homologyFunctorFactors` identifies
`Hⁿ(Q(K))` with `Hⁿ(K)`. -/
theorem isQuasicoherent_homologyFunctor_Q_obj (X : Scheme.{u})
    (K : CochainComplex X.Modules ℤ) (hK : ∀ i : ℤ, (K.X i).IsQuasicoherent) (n : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules n).obj
      (DerivedCategory.Q.obj K)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctorFactors X.Modules n).app K).symm
    ((SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isColimit_cokernelCofork
      (K.homologyIsCokernel ((ComplexShape.up ℤ).prev n) n rfl) (hK _)
      ((SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isLimit_kernelFork
        (K.cyclesIsKernel n ((ComplexShape.up ℤ).next n) rfl) (hK n) (hK _)))

/-- **[Stacks, Tag 08D3] in canonical form.** An object `E` of `D(𝒪_X)` with quasi-coherent
cohomology, whose tower of truncations from below has a product, *is* a derived limit of that
tower: there is a distinguished triangle
`E ⟶ ∏ τ_{≥ -n}E ⟶ ∏ τ_{≥ -n}E ⟶ E⟦1⟧` whose middle map is the Milnor difference map and whose
first map has the canonical truncation maps `π_{τ_{≥ -n}}` as its components.

`Stacks.TruncationTower.isIso_to_isDerivedLimit_truncGETower_of_isQuasicoherent` says that every
*presented* derived limit of the tower receives an isomorphism from `E`. The tower has some
derived limit `L` because the product exists; the canonical cone kills the difference map, by
compatibility of the truncation maps with the transitions, hence factors through `L`; the cited
form of the tag makes that factorization invertible; and the triangle of `L` is transported along
it. -/
theorem exists_isDerivedLimit_truncGETower_of_isQuasicoherent
    (X : Scheme.{u}) (E : DerivedCategory X.Modules)
    (hE : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj E).IsQuasicoherent)
    [HasProduct fun n : ℕ ↦ (truncGETower X.Modules E).obj ⟨n⟩] :
    ∃ (p : E ⟶ ∏ᶜ fun n : ℕ ↦ (truncGETower X.Modules E).obj ⟨n⟩)
      (δ : (∏ᶜ fun n : ℕ ↦ (truncGETower X.Modules E).obj ⟨n⟩) ⟶ E⟦(1 : ℤ)⟧),
      Triangle.mk p (Pi.lift fun n : ℕ ↦
          Pi.π (fun n : ℕ ↦ (truncGETower X.Modules E).obj ⟨n⟩) n -
            Pi.π (fun n : ℕ ↦ (truncGETower X.Modules E).obj ⟨n⟩) (n + 1) ≫
              (truncGETower X.Modules E).map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory X.Modules) ∧
        ∀ n : ℕ, p ≫ Pi.π (fun n : ℕ ↦ (truncGETower X.Modules E).obj ⟨n⟩) n =
          (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E := by
  obtain ⟨L, q, δ, hT⟩ := exists_isDerivedLimit (truncGETower X.Modules E)
  obtain ⟨u, hu⟩ : ∃ u : E ⟶ ∏ᶜ fun n : ℕ ↦ (truncGETower X.Modules E).obj ⟨n⟩,
      ∀ n : ℕ, u ≫ Pi.π (fun n : ℕ ↦ (truncGETower X.Modules E).obj ⟨n⟩) n =
        (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E :=
    ⟨Pi.lift fun n : ℕ ↦ (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E,
      fun n ↦ Pi.lift_comp_π _ n⟩
  have hu0 : u ≫ (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ (truncGETower X.Modules E).obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ (truncGETower X.Modules E).obj ⟨n⟩) (n + 1) ≫
          (truncGETower X.Modules E).map (homOfLE (Nat.le_succ n)).op) = 0 := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    rw [Category.assoc, Pi.lift_comp_π, Preadditive.comp_sub, hu n, ← Category.assoc, hu (n + 1),
      truncGETower_map_homOfLE_succ, zero_comp]
    exact sub_eq_zero_of_eq (TStructure.t.π_natTransTruncGEOfLE_app _ _ _ E).symm
  obtain ⟨c, hc0⟩ := Triangle.coyoneda_exact₂ _ hT u hu0
  dsimp only [Triangle.mk_mor₁] at hc0
  have hc : ∀ n : ℕ, c ≫ q ≫
      Pi.π (fun n : ℕ ↦ (truncGETower X.Modules E).obj ⟨n⟩) n =
        (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E := by
    intro n
    rw [← Category.assoc, ← hc0]
    exact hu n
  have hiso : IsIso c :=
    isIso_to_isDerivedLimit_truncGETower_of_isQuasicoherent X E hE L c q δ hT hc
  refine ⟨c ≫ q, δ ≫ (inv c)⟦(1 : ℤ)⟧', ?_, fun n ↦ (Category.assoc c q _).trans (hc n)⟩
  refine isomorphic_distinguished _ hT _ ?_
  refine Triangle.isoMk _ _ (asIso c) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · dsimp only [Triangle.mk_mor₁, Iso.refl_hom, asIso_hom]
    rw [Category.comp_id]
  · dsimp only [Triangle.mk_mor₂, Iso.refl_hom]
    rw [Category.comp_id, Category.id_comp]
  · dsimp only [Triangle.mk_mor₃, Iso.refl_hom, asIso_hom]
    rw [Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.comp_id, Category.id_comp]

end Stacks.TruncationTower

namespace AlgebraicGeometry

/-- **Unbounded affine vanishing from a tower of resolutions alone.** Let `M^•` be a cochain
complex of `R`-modules and write `E = Q(M̃^•)`. Suppose given

* a tower `𝓘 : ℕᵒᵖ ⥤ CochainComplex Mod(𝒪_{Spec R}) ℤ` whose `n`-th term is strictly `≥ -n` and
  has terms right acyclic for global sections (for instance: bounded below with injective terms);
* quasi-isomorphisms `g n : (τ_{≥ -n}M)^\sim ⟶ 𝓘ₙ`;
* isomorphisms `ι n : τ_{≥ -n}E ≅ Q(𝓘ₙ)` under which the canonical truncation map
  `E ⟶ τ_{≥ -n}E` becomes `Q(M̃^• ⟶ (τ_{≥ -n}M)^\sim ⟶ 𝓘ₙ)`;
* the compatibility of those composites with the transition maps of `𝓘`, in `D(𝒪_{Spec R})`.

Then the comparison `Q(Γ(Spec R, M̃^•)) ⟶ RΓ(E)` is an isomorphism, which is unbounded affine
vanishing for `M^•`.

This is `AlgebraicGeometry.isIso_globalSectionsComplexComparison_tilde_of_isDerivedLimit` with its
derived-limit hypothesis discharged. By
`Stacks.TruncationTower.exists_isDerivedLimit_truncGETower_of_isQuasicoherent` — [Stacks, Tag
08D3], whose quasi-coherence hypothesis holds because the terms of `M̃^•` are sheafifications —
the object `E` is a derived limit of its truncation tower with the canonical projections; the
isomorphisms `ι` commute with the successor transitions, by the extension property of `τ_{≥ -n}`
together with the two compatibilities assumed; and
`Stacks.DerivedLimit.exists_distTriang_of_towerIso` carries the triangle over to `𝓘 ⋙ Q`,
where its cone is the one the cited theorem asks for. -/
theorem isIso_globalSectionsComplexComparison_tilde_of_resolutionTower
    (R : CommRingCat.{u}) (M : CochainComplex (ModuleCat.{u} R) ℤ)
    (𝓘 : ℕᵒᵖ ⥤ CochainComplex (Spec R).Modules ℤ)
    (hGE : ∀ n : ℕ, (𝓘.obj ⟨n⟩).IsStrictlyGE (-(n : ℤ)))
    (hac : ∀ (n : ℕ) (i : ℤ),
      (globalSectionsOver (𝟙 (Spec R))).rightAcyclic ((𝓘.obj ⟨n⟩).X i))
    (g : ∀ n : ℕ, ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (M.truncGE (-(n : ℤ))) ⟶ 𝓘.obj ⟨n⟩)
    (hg : ∀ n : ℕ, QuasiIso (g n))
    (ι : ∀ n : ℕ, (truncGETower (Spec R).Modules (DerivedCategory.Q.obj
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M))).obj ⟨n⟩ ≅
      (𝓘 ⋙ DerivedCategory.Q).obj ⟨n⟩)
    (hι : ∀ n : ℕ, (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app
          (DerivedCategory.Q.obj
            (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) ≫
        (ι n).hom =
      DerivedCategory.Q.map (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (M.πTruncGE (-(n : ℤ))) ≫ g n))
    (hnat : ∀ n : ℕ, DerivedCategory.Q.map
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (M.πTruncGE (-((n + 1 : ℕ) : ℤ))) ≫ g (n + 1) ≫
            𝓘.map (homOfLE (Nat.le_succ n)).op) =
      DerivedCategory.Q.map (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (M.πTruncGE (-(n : ℤ))) ≫ g n))
    [HasProduct fun n : ℕ ↦ (truncGETower (Spec R).Modules (DerivedCategory.Q.obj
      (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M))).obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦ (𝓘 ⋙ DerivedCategory.Q).obj ⟨n⟩] :
    IsIso (globalSectionsComplexComparison (𝟙 (Spec R))
      (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) := by
  have hE : ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj
      (DerivedCategory.Q.obj
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M))).IsQuasicoherent :=
    fun n ↦ Stacks.TruncationTower.isQuasicoherent_homologyFunctor_Q_obj (Spec R) _
      (fun i ↦ inferInstanceAs ((tilde.functor R).obj (M.X i)).IsQuasicoherent) n
  have hsq : ∀ n : ℕ, (ι (n + 1)).hom ≫ (𝓘 ⋙ DerivedCategory.Q).map
        (homOfLE (Nat.le_succ n)).op =
      (truncGETower (Spec R).Modules (DerivedCategory.Q.obj
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M))).map
          (homOfLE (Nat.le_succ n)).op ≫ (ι n).hom := by
    intro n
    have hn : (𝓘.obj ⟨n⟩).IsStrictlyGE (-(n : ℤ)) := hGE n
    have h1 : ((𝓘 ⋙ DerivedCategory.Q).obj ⟨n⟩).IsGE (-(n : ℤ)) := by
      have := hn
      exact inferInstanceAs ((DerivedCategory.Q.obj (𝓘.obj ⟨n⟩)).IsGE (-(n : ℤ)))
    have h2 : DerivedCategory.TStructure.t.IsGE
        ((𝓘 ⋙ DerivedCategory.Q).obj ⟨n⟩) (-((n + 1 : ℕ) : ℤ)) :=
      DerivedCategory.TStructure.t.isGE_of_ge _ (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)
    have h3 := ((congrArg (fun z ↦
        (DerivedCategory.TStructure.t.truncGEπ (-((n + 1 : ℕ) : ℤ))).app
            (DerivedCategory.Q.obj (((tilde.functor R).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M)) ≫ z)
        (truncGETower_map_homOfLE_succ (Spec R).Modules (DerivedCategory.Q.obj
          (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) n)).trans
      (DerivedCategory.TStructure.t.π_natTransTruncGEOfLE_app _ _ _ _)).symm
    refine DerivedCategory.TStructure.t.from_truncGE_obj_ext ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun z ↦ z ≫ (𝓘 ⋙ DerivedCategory.Q).map
      (homOfLE (Nat.le_succ n)).op) (hι (n + 1))).trans ?_
    refine (DerivedCategory.Q.map_comp
      (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (M.πTruncGE (-((n + 1 : ℕ) : ℤ))) ≫ g (n + 1))
      (𝓘.map (homOfLE (Nat.le_succ n)).op)).symm.trans ?_
    refine (congrArg DerivedCategory.Q.map (Category.assoc _ _ _)).trans ?_
    refine (hnat n).trans ?_
    refine (hι n).symm.trans ?_
    refine (congrArg (fun z ↦ z ≫ (ι n).hom) h3).trans ?_
    exact Category.assoc _ _ _
  obtain ⟨p, δ, hT, hp⟩ :=
    Stacks.TruncationTower.exists_isDerivedLimit_truncGETower_of_isQuasicoherent (Spec R)
      (DerivedCategory.Q.obj
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) hE
  obtain ⟨p', δ', hT', hp'⟩ := Stacks.DerivedLimit.exists_distTriang_of_towerIso ι hsq p δ hT hp
  exact isIso_globalSectionsComplexComparison_tilde_of_isDerivedLimit R M 𝓘 hGE hac g hg p' δ' hT'
    fun n ↦ (hp' n).trans (hι n)

end AlgebraicGeometry

end
