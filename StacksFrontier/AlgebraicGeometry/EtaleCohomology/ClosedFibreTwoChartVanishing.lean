module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCharts
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MayerVietoris
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperHenselianFirstCohomology

/-!
# Vanishing above degree one on a scheme covered by two acyclic opens

Let `X` be a scheme covered by two open subschemes `U`, `V` and let `F` be an abelian sheaf on
the small étale site of `X` whose cohomology over `U`, over `V` and over `U ⊓ V` vanishes in
positive degrees. Then `H^q(X, F) = 0` for `q ≥ 2`.

Degree one is not reached, and that is not an artefact: the Mayer--Vietoris window
`H^0(U ⊓ V, F) ⟶ H^1(X, F) ⟶ H^1(U, F) ⊞ H^1(V, F)` exhibits `H^1(X, F)` as a quotient of
`H^0(U ⊓ V, F)`, which the hypotheses do not constrain.

The closed fibre of the projective line over a local ring is covered by two affine opens, the
preimages of the standard charts, which is the instance this vanishing is for.

## Main results

* `Stacks.EtaleCohomology.MayerVietoris.subsingleton_cohomologySup_of_subsingleton` — vanishing
  of the ambient Mayer--Vietoris term in degree `n₀ + 1` from vanishing over `U ⊓ V` in degree
  `n₀` and over `U` and `V` in degree `n₀ + 1`.
* `Stacks.EtaleCohomology.MayerVietoris.subsingleton_H_of_two_opens` — the same conclusion read
  as global étale cohomology when `U ⊔ V = ⊤`, hence vanishing in every degree `q ≥ 2` when the
  two opens and their intersection are acyclic in positive degrees.
* `Stacks.EtaleCohomology.sup_preimage_standardOpen_closedFibre_eq_top` and
  `Stacks.EtaleCohomology.isAffineOpen_preimage_standardOpen_closedFibre` — the closed fibre of
  the projective line over a local ring is the union of two affine opens.

## Implementation notes

Cohomology over an object of the site is `CategoryTheory.Sheaf.H'`, and the hypotheses are about
the objects `(opensToSite X).obj U` of the small étale site of `X`, not about the small étale
sites of `U` and of `V`. The comparison of the two is not available, so a hypothesis phrased as
acyclicity of the restriction of `F` to the chart cannot be consumed here;  the statements below
quantify over the degrees in the shape the Mayer--Vietoris sequence produces.

The site is the one-universe presentation `Stacks.EtaleCohomology.MayerVietoris.Site` of the
small étale site, which is where `Ext`, and hence cohomology over an object, is available;  see
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.MayerVietoris`.

## References

* [Stacks Project, Tag 0A50](https://stacks.math.columbia.edu/tag/0A50)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology.MayerVietoris

section Vanishing

variable {X : Scheme.{u}} (F : Sheaf (topology X) AddCommGrpCat.{u + 1}) (U V : X.Opens)

/-- **Vanishing of the ambient Mayer--Vietoris term.**  If the cohomology of `F` over `U ⊓ V`
vanishes in degree `n₀` and its cohomology over `U` and over `V` vanishes in degree `n₁ = n₀ + 1`,
then its cohomology over `U ⊔ V` vanishes in degree `n₁`.

Exactness of the window `H^{n₀}(U ⊓ V) ⟶ H^{n₁}(U ⊔ V) ⟶ H^{n₁}(U) ⊞ H^{n₁}(V)` makes the second
map a monomorphism, the first being zero on a vanishing source, and its target vanishes. -/
public theorem subsingleton_cohomologySup_of_subsingleton (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (hinter : Subsingleton (F.H' n₀ ((opensToSite X).obj (U ⊓ V))))
    (hU : Subsingleton (F.H' n₁ ((opensToSite X).obj U)))
    (hV : Subsingleton (F.H' n₁ ((opensToSite X).obj V))) :
    Subsingleton (F.H' n₁ ((opensToSite X).obj (U ⊔ V))) := by
  rw [← square_X₁ X U V] at hinter
  rw [← square_X₂ X U V] at hU
  rw [← square_X₃ X U V] at hV
  rw [← square_X₄ X U V]
  have hseq := cohomologySequence_exact F U V n₀ n₁ h
  have hExact := hseq.exact 2
  have hf0 : (hseq.sc 2).f = 0 := by
    apply AddCommGrpCat.Hom.ext
    ext a
    rw [show a = 0 from Subsingleton.elim (α := F.H' n₀ (square X U V).X₁) a 0]
    simp
  have hinj : Function.Injective (hseq.sc 2).g.hom :=
    (AddCommGrpCat.mono_iff_injective _).mp ((ShortComplex.exact_iff_mono _ hf0).mp hExact)
  have hs3 : Subsingleton (hseq.sc 2).X₃ :=
    AddCommGrpCat.subsingleton_of_isZero ((biprod_isZero_iff _ _).mpr
      ⟨AddCommGrpCat.isZero_of_subsingleton (G := F.H' n₁ (square X U V).X₂),
        AddCommGrpCat.isZero_of_subsingleton (G := F.H' n₁ (square X U V).X₃)⟩)
  exact ⟨fun a b => hinj (hs3.elim _ _)⟩

/-- **Vanishing above degree one from an acyclic cover by two opens.**  Let `X` be covered by two
open subschemes `U` and `V` and let `F` be an abelian sheaf on the small étale site of `X` whose
cohomology over `U`, over `V` and over `U ⊓ V` vanishes in every positive degree.  Then the global
étale cohomology `H^q(X, F)` vanishes for every `q ≥ 2`.

Degree one is not claimed:  the Mayer--Vietoris window at `q = 1` presents `H^1(X, F)` as a
quotient of `H^0(U ⊓ V, F)`, on which the hypotheses say nothing. -/
public theorem subsingleton_H_of_two_opens (hUV : U ⊔ V = ⊤)
    (hinter : ∀ n, 0 < n → Subsingleton (F.H' n ((opensToSite X).obj (U ⊓ V))))
    (hU : ∀ n, 0 < n → Subsingleton (F.H' n ((opensToSite X).obj U)))
    (hV : ∀ n, 0 < n → Subsingleton (F.H' n ((opensToSite X).obj V)))
    (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H.{u + 1} F q) := by
  obtain ⟨n₀, rfl⟩ : ∃ n₀, n₀ + 1 = q := ⟨q - 1, by omega⟩
  have hsup := subsingleton_cohomologySup_of_subsingleton F U V n₀ (n₀ + 1) rfl
    (hinter n₀ (by omega)) (hU _ (by omega)) (hV _ (by omega))
  rw [hUV] at hsup
  exact AddCommGrpCat.subsingleton_of_isZero
    (Limits.IsZero.of_iso (AddCommGrpCat.isZero_of_subsingleton
      (G := F.H' (n₀ + 1) ((opensToSite X).obj ⊤)))
      (cohomologyTopIsoH X F (n₀ + 1)).symm)

end Vanishing

end Stacks.EtaleCohomology.MayerVietoris

namespace Stacks.EtaleCohomology

/-! ### The closed fibre of the projective line is covered by two affine charts -/

private theorem fin_two_iSup {α : Type*} [CompleteLattice α] (g : Fin 2 → α) :
    (⨆ j, g j) = g 0 ⊔ g 1 :=
  le_antisymm (iSup_le fun j => by fin_cases j <;> simp)
    (sup_le (le_iSup g 0) (le_iSup g 1))

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- **The closed fibre of the projective line is the union of two opens.**  The preimages along
the closed-fibre inclusion of the two standard charts of `P¹_A` cover the closed fibre, the
standard charts covering `P¹_A`. -/
public theorem sup_preimage_standardOpen_closedFibre_eq_top :
    (closedFibreInclusion A ((projectiveSpaceOverRing 1 (.of A)) ↘ Spec (.of A)) ⁻¹ᵁ
        ProjectiveSpace.standardOpen 1 (Spec (.of A)) 0) ⊔
      (closedFibreInclusion A ((projectiveSpaceOverRing 1 (.of A)) ↘ Spec (.of A)) ⁻¹ᵁ
        ProjectiveSpace.standardOpen 1 (Spec (.of A)) 1) = ⊤ := by
  have h := Scheme.Hom.iSup_preimage_eq_top
    (closedFibreInclusion A ((projectiveSpaceOverRing 1 (.of A)) ↘ Spec (.of A)))
    (ProjectiveSpace.iSup_standardOpen_eq_top 1 (Spec (.of A)))
  rwa [fin_two_iSup] at h

/-- **The two charts of the closed fibre of the projective line are affine.**  The closed-fibre
inclusion is a closed immersion, hence an affine morphism, so the preimage of an affine open is
affine;  the standard charts of `P¹_A` are affine over an affine base. -/
public theorem isAffineOpen_preimage_standardOpen_closedFibre (i : Fin 2) :
    IsAffineOpen (closedFibreInclusion A ((projectiveSpaceOverRing 1 (.of A)) ↘ Spec (.of A)) ⁻¹ᵁ
      ProjectiveSpace.standardOpen 1 (Spec (.of A)) i) :=
  have : IsAffineHom (closedFibreInclusion A
      ((projectiveSpaceOverRing 1 (.of A)) ↘ Spec (.of A))) :=
    have : IsClosedImmersion (closedFibreInclusion A
        ((projectiveSpaceOverRing 1 (.of A)) ↘ Spec (.of A))) :=
      isClosedImmersion_closedFibreInclusion A _
    inferInstance
  (ProjectiveSpace.isAffineOpen_standardOpen 1 (Spec (.of A)) i).preimage _

/-- The preimage along the closed-fibre inclusion of the `i`-th standard chart of `P¹_A`, as an
open subscheme of the closed fibre. -/
public abbrev closedFibreChart (i : Fin 2) :
    (closedFibre A ((projectiveSpaceOverRing 1 (.of A)) ↘ Spec (.of A))).Opens :=
  closedFibreInclusion A ((projectiveSpaceOverRing 1 (.of A)) ↘ Spec (.of A)) ⁻¹ᵁ
    ProjectiveSpace.standardOpen 1 (Spec (.of A)) i

/-- **Higher étale cohomology on the closed fibre of the projective line, above degree one,
granted acyclicity of the two charts.**  Let `A` be a local ring, let `X = P¹_A` and let `X₀` be
the closed fibre of `X` over the closed point of `Spec A`.  If an abelian sheaf `F` on the small
étale site of `X₀` is acyclic in positive degrees over each of the two charts of `X₀` and over
their intersection, then `H^q(X₀, F) = 0` for every `q ≥ 2`.

The two charts cover `X₀` by
`Stacks.EtaleCohomology.sup_preimage_standardOpen_closedFibre_eq_top` and are affine by
`Stacks.EtaleCohomology.isAffineOpen_preimage_standardOpen_closedFibre`, which is what makes
`hcharts` the output of Gabber's affine variant of the proper base change theorem. -/
public theorem subsingleton_H_closedFibre_projectiveLine_of_charts_acyclic
    (F : Sheaf (MayerVietoris.topology
      (closedFibre A ((projectiveSpaceOverRing 1 (.of A)) ↘ Spec (.of A))))
      AddCommGrpCat.{u + 1})
    (hinter : ∀ n, 0 < n → Subsingleton (F.H' n ((MayerVietoris.opensToSite _).obj
      (closedFibreChart A 0 ⊓ closedFibreChart A 1))))
    (hchart : ∀ (i : Fin 2) (n : ℕ), 0 < n →
      Subsingleton (F.H' n ((MayerVietoris.opensToSite _).obj (closedFibreChart A i))))
    (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H.{u + 1} F q) :=
  MayerVietoris.subsingleton_H_of_two_opens F _ _
    (sup_preimage_standardOpen_closedFibre_eq_top A) hinter (hchart 0) (hchart 1) q hq

end Stacks.EtaleCohomology

end
