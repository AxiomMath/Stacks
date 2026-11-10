module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolution
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionClosedImmersion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FlatPartOverCdvrDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed

/-!
# A closed subspace of the base with the right open part and completion is a solution

In the situation of Stacks 0GH8, recorded by `AlgebraicGeometry.Artin.ContractionSituation`,
let `X' → S` be proper and let `Z ⊆ S` be a closed subset with inverse image `T'` in `X'`, such
that `U' → S ∖ Z` and `W → S_{/Z}` are closed immersions. The first paragraph of the proof of
**Stacks 0GHE** observes that a closed subscheme `X ⊆ S` with `X ∩ (S ∖ Z) = U'` and
`X_{/Z} = W` is a solution. This file proves that observation, with `X` a closed subspace of
the terminal presheaf (the algebraic space `S`) containing the image of `X'`.

The proof uses that everything in sight is *subterminal*: the completion `S_{/Z}` is a
subsheaf of the terminal sheaf, `W` and `X_{/T}` are subsheaves of `S_{/Z}` through the closed
immersions `W → S_{/Z}` and `X_{/T} → S_{/Z}`, so two morphisms into any of them agree. This
makes the isomorphism `a : X_{/T} ≅ W` and condition (3) of a solution automatic once morphisms
in both directions exist.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.hom_ext_completionSheaf_terminal`: two
  morphisms into the completion `S_{/Z}` of the terminal presheaf agree.
* `AlgebraicGeometry.Artin.ContractionSituation.solution_of_isClosedSubspace`: the solution
  attached to a closed subspace `X ⊆ S` with `X ∩ (S ∖ Z) = U'` and `X_{/Z} = W`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The values of the terminal presheaf on the big fppf site of `S` are subsingletons. -/
theorem subsingleton_terminal_obj (V : (BigFppfOver B S hS)ᵒᵖ) :
    Subsingleton ((⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)).obj V) := by
  induction V using Opposite.rec with
  | op V => exact ⟨fun x y => yonedaEquiv.symm.injective (terminal.hom_ext _ _)⟩

/-- The values of the universe lift of the terminal presheaf are subsingletons. -/
private theorem subsingleton_terminal_comp_uliftFunctor_obj (W : (BigFppfOver B S hS)ᵒᵖ) :
    Subsingleton (((⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) ⋙ uliftFunctor.{u + 1}).obj W) := by
  have := subsingleton_terminal_obj (B := B) (S := S) (hS := hS) W
  exact ⟨fun a b => ULift.ext (Subsingleton.elim _ _)⟩

/-- The universe lift of the terminal presheaf is an fppf sheaf: its values are subsingletons
and inhabited, so every matching family has exactly one amalgamation. -/
theorem isSheaf_terminal_comp_uliftFunctor :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      ((⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) ⋙ uliftFunctor.{u + 1}) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro V R _ x _
  let t : ((⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) ⋙ uliftFunctor.{u + 1}).obj (Opposite.op V) :=
    ⟨yonedaEquiv (terminal.from (yoneda.obj V))⟩
  have hsub := subsingleton_terminal_comp_uliftFunctor_obj (B := B) (S := S) (hS := hS)
  exact ⟨t, fun _ _ _ => (hsub _).elim _ _, fun _ _ => (hsub _).elim _ _⟩

/-- Two morphisms into the sheafified universe lift of the terminal presheaf agree. -/
theorem hom_ext_sheafifiedULift_terminal {F : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    (f g : F ⟶ Space.sheafifiedULift B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))) :
    f = g := by
  let e := (BigFppfOver.topology B S hS).isoSheafify
    (isSheaf_terminal_comp_uliftFunctor (B := B) (S := S) (hS := hS))
  apply Sheaf.hom_ext
  have h : (f.hom ≫ e.inv : F.obj ⟶ _) = g.hom ≫ e.inv := by
    ext V x
    exact (subsingleton_terminal_comp_uliftFunctor_obj V).elim _ _
  exact (cancel_mono e.inv).1 h

/-- Two morphisms into the completion `S_{/Z}` of the terminal presheaf along a set `Z` of
points agree: `S_{/Z}` is a subsheaf of the terminal sheaf. -/
theorem hom_ext_completionSheaf_terminal {F : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    (Z : Set (Space.points B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))))
    (f g : F ⟶ Space.completionSheaf B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Z) :
    f = g := by
  have := Space.mono_completionSheafInclusion B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Z
  rw [← cancel_mono (Space.completionSheafInclusion B S hS _ Z)]
  exact hom_ext_sheafifiedULift_terminal _ _

/-- Two morphisms into a sheaf with a monomorphism to `S_{/Z}` agree. -/
theorem hom_ext_of_mono_completionSheaf_terminal
    {F W : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    (Z : Set (Space.points B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))))
    (w : W ⟶ Space.completionSheaf B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Z) [Mono w]
    (f g : F ⟶ W) : f = g := by
  rw [← cancel_mono w]
  exact hom_ext_completionSheaf_terminal Z _ _

/-- A morphism `ρ : A ⟶ G` of presheaves of types is an isomorphism if, for monomorphisms
`j : G ⟶ E` and `v = ρ ≫ j`, the range of `j` is contained in the range of `v`. -/
private theorem isIso_of_comp_eq_of_range_le {C : Type*} [Category C] {A G E : Cᵒᵖ ⥤ Type u}
    (ρ : A ⟶ G) (j : G ⟶ E) [Mono j] (v : A ⟶ E) [Mono v] (h : ρ ≫ j = v)
    (hr : Subfunctor.range j ≤ Subfunctor.range v) : IsIso ρ := by
  have : Mono (ρ ≫ j) := by
    rw [h]
    infer_instance
  have := mono_of_mono ρ j
  rw [NatTrans.isIso_iff_isIso_app]
  intro V
  rw [isIso_iff_bijective]
  refine ⟨(mono_iff_injective (ρ.app V)).1 inferInstance, fun y => ?_⟩
  obtain ⟨z, hz⟩ := hr V ⟨y, rfl⟩
  exact ⟨z, (mono_iff_injective (j.app V)).1 inferInstance
    ((congrArg (fun φ => φ.app V z) h).trans hz)⟩

/-- **The first paragraph of the proof of Stacks 0GHE.** In the situation of Stacks 0GH8 let
`X' → S` be proper, let `Z ⊆ |S|` be closed with inverse image `T'` in `X'`, and let
`U' → S ∖ Z` and `W → S_{/Z}` be closed immersions. A closed subspace `X` of `S` through which
`X' → S` factors, with `X ∩ (S ∖ Z)` the image of `U'` and with morphisms in both directions
between `W` and the completion `X_{/T}` of `X` along `T = X ∩ Z`, is a solution whose open
subspace `U` is `X ∖ T`, and `X → S` is a closed immersion. -/
theorem solution_of_isClosedSubspace (c : ContractionSituation B S hS)
    (hproper : Space.IsProper B S hS (terminal.from c.X'))
    (Z : Set (Space.points B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))))
    (hZ : IsClosed Z)
    (hT' : Space.pointsMap B S hS c.X' (terminal.from c.X') ⁻¹' Z = c.T')
    (u : c.U'.toFunctor ⟶ (Space.openSubspaceOfPoints B S hS _ Zᶜ).toFunctor)
    (hu : Space.IsClosedImmersion B S hS u)
    (w : c.W ⟶ Space.completionSheaf B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Z)
    (hw : FormalSpace.IsClosedImmersion B S hS w)
    (X : Subfunctor (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)))
    (hX : Space.IsClosedSubspace B S hS X)
    (hX' : Subfunctor.range (terminal.from c.X') ≤ X)
    (hXU : X ⊓ Space.openSubspaceOfPoints B S hS _ Zᶜ =
      Subfunctor.range (u ≫ (Space.openSubspaceOfPoints B S hS _ Zᶜ).ι))
    (hXW : Nonempty (c.W ⟶
      Space.completionSheaf B S hS X.toFunctor (Space.pointsMap B S hS X.toFunctor X.ι ⁻¹' Z)))
    (hWX : Nonempty (Space.completionSheaf B S hS X.toFunctor
      (Space.pointsMap B S hS X.toFunctor X.ι ⁻¹' Z) ⟶ c.W)) :
    (∃ s : c.Solution X.toFunctor,
      Set.range (Space.pointsMap B S hS s.U.toFunctor s.U.ι) = s.Tᶜ) ∧
      Space.IsClosedImmersion B S hS (terminal.from X.toFunctor) := by
  classical
  let one := ⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  have hone : IsAlgebraicSpace B S hS one := Space.isAlgebraicSpace_terminal B S hS
  let f : c.X' ⟶ X.toFunctor := Subfunctor.lift (terminal.from c.X') hX'
  have hfι : f ≫ X.ι = terminal.from c.X' := Subfunctor.lift_ι _ _
  let T : Set (Space.points B S hS X.toFunctor) := Space.pointsMap B S hS X.toFunctor X.ι ⁻¹' Z
  have hTclosed : IsClosed T := hZ.preimage (Space.continuous_pointsMap B S hS X.ι)
  have hpre : Space.pointsMap B S hS c.X' f ⁻¹' T = c.T' := by
    change Space.pointsMap B S hS c.X' f ⁻¹' (Space.pointsMap B S hS X.toFunctor X.ι ⁻¹' Z) = _
    rw [← Set.preimage_comp, ← Space.pointsMap_comp, hfι, hT']
  let U := Space.openSubspaceOfPoints B S hS X.toFunctor Tᶜ
  let ρ : c.U'.toFunctor ⟶ U.toFunctor :=
    Space.openSubspaceOfPointsRestrict B S hS f c.T'ᶜ Tᶜ (by rw [Set.preimage_compl, hpre])
  have hρ_one : ρ ≫ U.ι ≫ X.ι = u ≫ (Space.openSubspaceOfPoints B S hS one Zᶜ).ι :=
    terminal.hom_ext _ _
  have := Space.mono_of_isClosedImmersion B S hS u hu
  have hρiso : IsIso ρ := isIso_of_comp_eq_of_range_le ρ (U.ι ≫ X.ι) _ hρ_one (by
    rintro V _ ⟨y, rfl⟩
    rw [← hXU]
    exact ⟨y.1.2, ((Space.openSubspaceOfPointsRestrict B S hS X.ι Tᶜ Zᶜ fun _ => id).app V y).2⟩)
  have hWmono : Mono w := FormalSpace.mono_of_isClosedImmersion B S hS w hw
  have hXTmono : Mono (Space.completionSheafMap B S hS X.ι Z) :=
    FormalSpace.mono_of_isClosedImmersion B S hS _
      (FormalSpace.isClosedImmersion_completionSheafMap B S hS hX.1 hone X.ι Z hX.2)
  obtain ⟨φ⟩ := hXW
  obtain ⟨ψ⟩ := hWX
  refine ⟨⟨{ isAlgebraicSpace_X := hX.1
             f := f
             isProper_f := Space.isProper_of_comp_of_isSeparated B S hS c.isAlgebraicSpace_X'
               hX.1 hone f X.ι (by rwa [hfι])
               (Space.isSeparated_of_isClosedImmersion B S hS X.ι hX.2)
             T := T
             isClosed_T := hTclosed
             preimage_T := hpre
             U := U
             isOpenSubspace_U :=
               Space.isOpenSubspace_openSubspaceOfPoints B S hS hX.1 Tᶜ hTclosed.isOpen_compl
             isoU := asIso ρ
             isoU_comp_ι := rfl
             a :=
               { hom := ψ
                 inv := φ
                 hom_inv_id := hom_ext_of_mono_completionSheaf_terminal Z
                   (Space.completionSheafMap B S hS X.ι Z) _ _
                 inv_hom_id := hom_ext_of_mono_completionSheaf_terminal Z w _ _ }
             completion_comp_a := hom_ext_of_mono_completionSheaf_terminal Z w _ _ },
    Space.range_pointsMap_ι_openSubspaceOfPoints B S hS Tᶜ⟩, ?_⟩
  rw [show terminal.from X.toFunctor = X.ι from terminal.hom_ext _ _]
  exact hX.2

end AlgebraicGeometry.Artin.ContractionSituation
