module

public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import StacksFrontier.Algebra.DifferentialGraded.Module.DGCategoryClosedMaps
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHomPrecompositionFunctor
public import StacksFrontier.Algebra.DifferentialGraded.Module.PropertyP
public import StacksFrontier.Algebra.DifferentialGraded.Module.QuasiIsomorphism
public import StacksFrontier.Algebra.DifferentialGraded.Module.Triangulated
public import StacksCore.Tactic.StacksAttribute

/-! # Precomposition into a right-orthogonal module is a quasi-isomorphism

Let `f : M → N` be a homomorphism of differential graded `(A, B)`-bimodules whose underlying
homomorphism of right differential graded `B`-modules is a quasi-isomorphism, and let `I` be a
right differential graded `B`-module whose class in `K(B)` is orthogonal on the right to the
acyclic modules — for instance a module with property (I), by Tag 09KS. Then precomposition

  `Hom^•_B(N, I) ⟶ Hom^•_B(M, I)`

is a quasi-isomorphism of differential graded `A`-modules.

This is the second assertion of Tag 0BYV at the level where it is actually proved: once the
derived Hom functor is computed by such modules, it says that the derived transformation is an
isomorphism.

## Main results

* `DifferentialGraded.Bimodule.isQuasiIsomorphism_precompModuleHom` and
  `DifferentialGraded.Bimodule.quasiIso_precompModuleHom`: the statement above, in the
  cycle-and-boundary form of `DifferentialGradedModule.IsQuasiIsomorphism` and in Mathlib's
  `QuasiIso` form.

## Implementation notes

*The proof is not the source's.* Stacks 0BYV filters `I` and reduces to shifts of `B^∨` through
an `Rlim` argument. Here the hypothesis on `I` is used directly: orthogonality on the right to
the acyclic modules says exactly that `I` is a local object for the quasi-isomorphisms
(`CategoryTheory.ObjectProperty.isLocal_trW`), i.e. that precomposition with a quasi-isomorphism
is a *bijection* on morphisms of `K(B)` into `I`; and the right orthogonal of a triangulated
subcategory is stable under shifts, so the same holds with `I` replaced by any shift of it. The
cohomology of the Hom complex is morphisms in `K(B)` into a shift, which is Tag 09LC, so the two
cycle-and-boundary conditions are precisely the injectivity and the surjectivity of those
bijections. No filtration of `I` and no `Rlim` is needed; what the source's argument establishes
is the *existence* of resolutions by such modules, which is Tag 09KU and is separate.

*The dictionary.* The degree-`n` piece of a presentation of `Hom^•_B(X, I)` is the degree-`n`
homogeneous right `B`-linear maps `X → I`; a cocycle there is a homomorphism `X ⟶ I[n]` with the
same underlying linear map, and a coboundary is a null-homotopic one. Those two translations are
`DifferentialGradedModule.homogeneousMapDifferential_eq_zero_iff_exists_hom_shift` and
`DifferentialGradedModule.homotopic_zero_iff_exists_homogeneousMapDifferential`, both Tag 09LC;
the lemmas in the `HomModuleData` namespace below carry them across the presentation's
identification of the graded pieces.

## References

* [Stacks Project, Tag 0BYV](https://stacks.math.columbia.edu/tag/0BYV); the identification of
  Hom cohomology with homotopy classes is [Tag 09LC](https://stacks.math.columbia.edu/tag/09LC),
  the orthogonality of modules with property (I) is
  [Tag 09KS](https://stacks.math.columbia.edu/tag/09KS), and the quasi-isomorphisms as the
  multiplicative system of the acyclic modules are
  [Tag 09KW](https://stacks.math.columbia.edu/tag/09KW).
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}

/-- A homomorphism of differential graded modules is null-homotopic exactly when its homotopy
class vanishes. -/
theorem toHomotopyCategory_map_eq_zero_iff {X Y : DifferentialGradedModule A} (G : X ⟶ Y) :
    (toHomotopyCategory A).map G = 0 ↔ Homotopic G 0 := by
  rw [show (0 : (toHomotopyCategory A).obj X ⟶ (toHomotopyCategory A).obj Y) =
      (toHomotopyCategory A).map 0 from ((toHomotopyCategory A).map_zero X Y).symm]
  exact CategoryTheory.Quotient.functor_map_eq_iff (homotopyRel A) G 0

/-- Two homomorphisms of differential graded modules are homotopic exactly when their difference
is null-homotopic. -/
theorem homotopic_iff_sub_homotopic_zero {X Y : DifferentialGradedModule A} (G H : X ⟶ Y) :
    Homotopic G H ↔ Homotopic (G - H) 0 := by
  have h₁ : Homotopic G H ↔ (toHomotopyCategory A).map G = (toHomotopyCategory A).map H :=
    (CategoryTheory.Quotient.functor_map_eq_iff (homotopyRel A) G H).symm
  have h₂ : Homotopic (G - H) 0 ↔ (toHomotopyCategory A).map (G - H) = 0 :=
    (toHomotopyCategory_map_eq_zero_iff (G - H)).symm
  rw [h₁, h₂, (toHomotopyCategory A).map_sub, sub_eq_zero]

namespace HomModuleData

variable {X I : DifferentialGradedModule B} {LX : BimoduleStructure A B X}
  (H : HomModuleData A B X I LX)

/-- Elements of two graded pieces of equal degree have the same underlying element exactly when
they present the same homogeneous map. -/
theorem homogeneousEquiv_val_eq_iff {i j : ℤ} (hij : i = j) (a : H.module.grading i)
    (b : H.module.grading j) :
    (H.homogeneousEquiv i a).1 = (H.homogeneousEquiv j b).1 ↔
      (a : H.module.M) = (b : H.module.M) := by
  subst hij
  exact ⟨fun h => congrArg Subtype.val ((H.homogeneousEquiv i).injective (Subtype.ext h)),
    fun h => congrArg (fun c => (H.homogeneousEquiv i c).1) (Subtype.ext h)⟩

/-- A homogeneous element of a presentation of the internal hom is a cocycle exactly when the
homogeneous map it presents is closed. -/
theorem d_eq_zero_iff (n : ℤ) (g : H.module.grading n) :
    H.module.d (g : H.module.M) = 0 ↔
      homogeneousMapDifferential B (H.homogeneousEquiv n g) = 0 := by
  rw [← H.map_d n g]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [show H.module.gradedDifferential n g = 0 from Subtype.ext h, map_zero]
  · exact congrArg Subtype.val
      ((H.homogeneousEquiv (n + 1)).injective (h.trans (map_zero _).symm))

/-- A homogeneous element of a presentation of the internal hom is a coboundary exactly when the
homogeneous map it presents is a boundary for the Hom differential. -/
theorem exists_d_eq_iff (n : ℤ) (g : H.module.grading n) :
    (∃ z ∈ H.module.grading (n - 1), H.module.d z = (g : H.module.M)) ↔
      ∃ h : HomogeneousMap B X I (n - 1),
        (homogeneousMapDifferential B h).1 = (H.homogeneousEquiv n g).1 := by
  refine ⟨fun ⟨z, hz, hdz⟩ => ⟨H.homogeneousEquiv (n - 1) ⟨z, hz⟩, ?_⟩, fun ⟨h, hh⟩ => ?_⟩
  · rw [← H.map_d (n - 1) ⟨z, hz⟩]
    exact (H.homogeneousEquiv_val_eq_iff (by omega) _ g).2 hdz
  · refine ⟨((H.homogeneousEquiv (n - 1)).symm h : H.module.M),
      ((H.homogeneousEquiv (n - 1)).symm h).property, ?_⟩
    have hd := H.map_d (n - 1) ((H.homogeneousEquiv (n - 1)).symm h)
    rw [LinearEquiv.apply_symm_apply] at hd
    exact (H.homogeneousEquiv_val_eq_iff (show n - 1 + 1 = n by omega) _ g).1
      ((congrArg Subtype.val hd).trans hh)

/-- **Tag 09LC** through a presentation: a degree-`n` cocycle of the internal hom is a
homomorphism into the `n`-fold shift of the target with the same underlying linear map. -/
theorem exists_hom_shift (n : ℤ) (g : H.module.grading n)
    (hg : H.module.d (g : H.module.M) = 0) :
    ∃ G : X ⟶ shift I n, G.toFun = (H.homogeneousEquiv n g).1 :=
  (homogeneousMapDifferential_eq_zero_iff_exists_hom_shift B X I n
    (H.homogeneousEquiv n g)).1 ((H.d_eq_zero_iff n g).1 hg)

/-- **Tag 09LC** through a presentation, in the other direction: a homomorphism into the `n`-fold
shift of the target is a degree-`n` cocycle of the internal hom. -/
theorem exists_grading (n : ℤ) (G : X ⟶ shift I n) :
    ∃ g : H.module.grading n, H.module.d (g : H.module.M) = 0 ∧
      (H.homogeneousEquiv n g).1 = G.toFun := by
  have hmem : G.toFun ∈ homogeneousMapSubmodule B X I n := by
    refine ⟨fun i x hx => ?_, fun a x => G.map_smul x a⟩
    simpa only [shift_grading] using G.map_grading i x hx
  refine ⟨(H.homogeneousEquiv n).symm ⟨G.toFun, hmem⟩, ?_, ?_⟩
  · rw [H.d_eq_zero_iff n, LinearEquiv.apply_symm_apply]
    exact (homogeneousMapDifferential_eq_zero_iff_exists_hom_shift B X I n
      ⟨G.toFun, hmem⟩).2 ⟨G, rfl⟩
  · rw [LinearEquiv.apply_symm_apply]

/-- **Tag 09LC** through a presentation: a degree-`n` cocycle of the internal hom is a
coboundary exactly when the corresponding homomorphism into the `n`-fold shift of the target is
null-homotopic. -/
theorem exists_d_eq_iff_homotopic_zero (n : ℤ) (g : H.module.grading n) (G : X ⟶ shift I n)
    (hG : G.toFun = (H.homogeneousEquiv n g).1) :
    (∃ z ∈ H.module.grading (n - 1), H.module.d z = (g : H.module.M)) ↔ Homotopic G 0 :=
  (H.exists_d_eq_iff n g).trans
    (homotopic_zero_iff_exists_homogeneousMapDifferential B (H.homogeneousEquiv n g) G hG).symm

end HomModuleData

end DifferentialGradedModule

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R} {M N : Bimodule A B}

/-- The homogeneous map presented by precomposition with `f` is the composite with `f` of the
homogeneous map presented by the argument, read as a homomorphism into a shift. -/
private theorem precompGraded_hom_shift (f : M ⟶ N) {I : DifferentialGradedModule B} (n : ℤ)
    (g : (homPresentation N I).module.grading n) (G : N.rightModule ⟶ shift I n)
    (hG : G.toFun = ((homPresentation N I).homogeneousEquiv n g).1) :
    (f.rightHom ≫ G).toFun =
      ((homPresentation M I).homogeneousEquiv n
        (precompGraded f (homPresentation N I) (homPresentation M I) n g)).1 := by
  apply LinearMap.ext
  intro z
  rw [precompGraded_apply]
  change G.toFun (f.rightHom.toFun z) = _
  rw [hG]

/-- The right orthogonal of the acyclic modules is stable under shifts, and the shift of the
image of a module in the homotopy category is the image of its shift. -/
private theorem rightOrthogonal_acyclic_shift {I : DifferentialGradedModule B}
    (hI : (acyclic' B).rightOrthogonal ((toHomotopyCategory B).obj I)) (n : ℤ) :
    (acyclic' B).rightOrthogonal ((toHomotopyCategory B).obj (shift I n)) := by
  have hshift : (((toHomotopyCategory B).obj I)⟦n⟧) =
      (toHomotopyCategory B).obj (shift I n) := by
    change ((CategoryTheory.shiftFunctor (HomotopyCategory B) n).obj
        ((toHomotopyCategory B).obj I)) =
      (toHomotopyCategory B).obj
        ((CategoryTheory.shiftFunctor (DifferentialGradedModule B) n).obj I)
    exact CategoryTheory.Quotient.functor_obj_shift (homotopyRel B) ℤ I n
  rw [← hshift]
  exact ObjectProperty.le_shift (acyclic' B).rightOrthogonal n _ hI

/-- Precomposition with a quasi-isomorphism is a bijection on homotopy classes of homomorphisms
into a shift of a module orthogonal on the right to the acyclic modules. -/
private theorem bijective_comp_of_rightOrthogonal (f : M ⟶ N)
    (hf : QuasiIso ((forgetToCochainComplex B).map f.rightHom))
    {I : DifferentialGradedModule B}
    (hI : (acyclic' B).rightOrthogonal ((toHomotopyCategory B).obj I)) (n : ℤ) :
    Function.Bijective
      (fun G : (toHomotopyCategory B).obj N.rightModule ⟶
          (toHomotopyCategory B).obj (shift I n) =>
        (toHomotopyCategory B).map f.rightHom ≫ G) := by
  have hlocal : (quasiIsomorphisms' B).isLocal ((toHomotopyCategory B).obj (shift I n)) := by
    rw [← acyclic_trW_eq_quasiIsomorphisms', ObjectProperty.isLocal_trW]
    exact rightOrthogonal_acyclic_shift hI n
  exact hlocal _ ((quasiIsomorphisms_map_iff' B f.rightHom).2 hf)

/-- The key step towards the second assertion of Tag 0BYV, in cycle-and-boundary form.
If `f : M ⟶ N` is a homomorphism of differential graded
`(A, B)`-bimodules which is a quasi-isomorphism of the underlying differential graded
`B`-modules, and `I` is a right differential graded `B`-module whose class in `K(B)` is
orthogonal on the right to the acyclic modules, then precomposition with `f` is a
quasi-isomorphism `Hom^•_B(N, I) ⟶ Hom^•_B(M, I)`. -/
theorem isQuasiIsomorphism_precompModuleHom (f : M ⟶ N)
    (hf : QuasiIso ((forgetToCochainComplex B).map f.rightHom))
    (I : DifferentialGradedModule B)
    (hI : (acyclic' B).rightOrthogonal ((toHomotopyCategory B).obj I)) :
    IsQuasiIsomorphism (precompModuleHom f I) := by
  intro n
  have hbij := bijective_comp_of_rightOrthogonal f hf hI n
  constructor
  · -- every cocycle of `Hom^•_B(M, I)` is, modulo a coboundary, the image of a cocycle
    intro y hy hdy
    obtain ⟨Hy, hHy⟩ := (homPresentation M I).exists_hom_shift n ⟨y, hy⟩ hdy
    obtain ⟨c, hc⟩ := hbij.2 ((toHomotopyCategory B).map Hy)
    obtain ⟨G, rfl⟩ : ∃ G : N.rightModule ⟶ shift I n, (toHomotopyCategory B).map G = c :=
      Quot.inductionOn c (fun g => ⟨g, rfl⟩)
    obtain ⟨x, hdx, hxval⟩ := (homPresentation N I).exists_grading n G
    refine ⟨(x : (homPresentation N I).module.M), x.property, hdx, ?_⟩
    -- the difference is a coboundary because the two homomorphisms are homotopic
    have hsub : (Hy - f.rightHom ≫ G).toFun =
        ((homPresentation M I).homogeneousEquiv n
          (⟨y, hy⟩ - precompGraded f (homPresentation N I) (homPresentation M I) n x)).1 := by
      rw [map_sub, Hom.hom_sub_toFun, hHy, precompGraded_hom_shift f n x G hxval.symm]
      rfl
    obtain ⟨z, hz, hdz⟩ :=
      ((homPresentation M I).exists_d_eq_iff_homotopic_zero n
        (⟨y, hy⟩ - precompGraded f (homPresentation N I) (homPresentation M I) n x)
        (Hy - f.rightHom ≫ G) hsub).2
        ((toHomotopyCategory_map_eq_zero_iff _).1
          (by
            rw [(toHomotopyCategory B).map_sub, (toHomotopyCategory B).map_comp]
            exact sub_eq_zero.2 hc.symm))
    refine ⟨z, hz, ?_⟩
    rw [hdz]
    change y - _ = y - (precompModuleHom f I).toFun (x : (homPresentation N I).module.M)
    rw [precompModuleHom_apply_grading f I n x]
  · -- a cocycle whose image is a coboundary is itself a coboundary
    intro x hx hdx ⟨z, hz, hdz⟩
    obtain ⟨G, hG⟩ := (homPresentation N I).exists_hom_shift n ⟨x, hx⟩ hdx
    have hzero : Homotopic (f.rightHom ≫ G) 0 :=
      ((homPresentation M I).exists_d_eq_iff_homotopic_zero n
        (precompGraded f (homPresentation N I) (homPresentation M I) n ⟨x, hx⟩)
        (f.rightHom ≫ G) (precompGraded_hom_shift f n ⟨x, hx⟩ G hG)).1
        ⟨z, hz, by rw [hdz, ← precompModuleHom_apply_grading f I n ⟨x, hx⟩]⟩
    have hGzero : (toHomotopyCategory B).map G = 0 := by
      refine hbij.1 ?_
      change (toHomotopyCategory B).map f.rightHom ≫ (toHomotopyCategory B).map G =
        (toHomotopyCategory B).map f.rightHom ≫ 0
      rw [Limits.comp_zero, ← (toHomotopyCategory B).map_comp]
      exact (toHomotopyCategory_map_eq_zero_iff (f.rightHom ≫ G)).2 hzero
    exact ((homPresentation N I).exists_d_eq_iff_homotopic_zero n ⟨x, hx⟩ G hG).2
      ((toHomotopyCategory_map_eq_zero_iff G).1 hGzero)

/-- The key step towards the second assertion of Tag 0BYV, in Mathlib's
form: precomposition with a quasi-isomorphism of bimodules is a quasi-isomorphism of the
underlying cochain complexes of the internal homs into a module orthogonal on the right to the
acyclic modules. -/
theorem quasiIso_precompModuleHom (f : M ⟶ N)
    (hf : QuasiIso ((forgetToCochainComplex B).map f.rightHom))
    (I : DifferentialGradedModule B)
    (hI : (acyclic' B).rightOrthogonal ((toHomotopyCategory B).obj I)) :
    QuasiIso ((forgetToCochainComplex A).map (precompModuleHom f I)) :=
  quasiIso_of_isQuasiIsomorphism (precompModuleHom f I)
    (isQuasiIsomorphism_precompModuleHom f hf I hI)

end DifferentialGraded.Bimodule

end
