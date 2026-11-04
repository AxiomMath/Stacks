module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierKernel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseSheafPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSheaf.TwistInverseImage

/-!
# Inverse images of the Artin–Schreier kernel

For a `k`-algebra map `φ : A → A'` with `Spec A`, `Spec A'` connected, the inverse image of the
Artin–Schreier sheaf `L_ψ(g)` with coefficients in a finite commutative ring `Λ` along
`Spec φ : Spec A' → Spec A` is `L_ψ(φ g)`: the inverse image of a lisse sheaf is the lisse sheaf of
the restricted representation
(`Stacks.EtaleCohomology.nonempty_etaleModuleInverseImage_lisseEtaleSheaf_iso`), and the
Artin–Schreier character of `φ g` is that of `g` composed with `π₁(Spec A') → π₁(Spec A)`
(`Stacks.ArtinSchreier.artinSchreierCharacter_map`).

## Main results

* `Stacks.ArtinSchreier.nonempty_etaleModuleInverseImage_artinSchreierLevelSheaf_iso`: the
  inverse image of `L_ψ(g)` along `Spec φ` is isomorphic to `L_ψ(φ g)`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.EtaleCohomology Stacks.GroupCohomology

universe u

namespace Stacks.ArtinSchreier

variable (k : Type u) [Field k] [Fintype k] {A : Type u} [CommRing A] [Algebra k A] (g : A)
  {A' : Type u} [CommRing A'] [Algebra k A'] (φ : A →ₐ[k] A')
  [ConnectedSpace (Spec (.of A))] [ConnectedSpace (Spec (.of A'))]
  (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ) (B : BigEtaleSite.{u})
  (hX : schemeSizeBelow B.cutoff (Spec (.of A))) (hX' : schemeSizeBelow B.cutoff (Spec (.of A')))

/-- The inverse image of `L_ψ(g)` along `Spec φ` is isomorphic to `L_ψ(φ g)`, for any points of the
fibres of the two Artin–Schreier covers. -/
theorem nonempty_etaleModuleInverseImage_artinSchreierLevelSheaf_iso
    (y : GeometricPoint (Spec (.of A')))
    (p₀ : (finiteEtaleFiberFunctor (y.map (Spec.map (CommRingCat.ofHom φ.toRingHom)))).obj
      (cover k A g))
    (p₀' : (finiteEtaleFiberFunctor y).obj (cover k A' (φ g))) :
    Nonempty ((etaleModuleInverseImage.{u, 0} Λ (Spec.map (CommRingCat.ofHom φ.toRingHom))).obj
        (artinSchreierLevelSheaf k A g Λ ψ B hX
          (y.map (Spec.map (CommRingCat.ofHom φ.toRingHom))) p₀) ≅
      artinSchreierLevelSheaf k A' (φ g) Λ ψ B hX' y p₀') := by
  have : ConnectedSpace (specObject A B hX).1 := inferInstanceAs (ConnectedSpace (Spec (.of A)))
  have : ConnectedSpace (specObject A' B hX').1 :=
    inferInstanceAs (ConnectedSpace (Spec (.of A')))
  let f : specObject A' B hX' ⟶ specObject A B hX :=
    ObjectProperty.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom))
  obtain ⟨e⟩ := nonempty_etaleModuleInverseImage_lisseEtaleSheaf_iso B f y Λ
    (characterContinuousModule Λ (artinSchreierCharacter k A g ψ (y.map f.hom) p₀)
      (isOpen_ker_artinSchreierCharacter k A g Λ ψ (y.map f.hom) p₀))
  have hχ := artinSchreierCharacter_map k g φ ψ y p₀' p₀
  refine ⟨e ≪≫ (lisseEtaleSheaf B (specObject A' B hX') y Λ).mapIso
    (finiteTypeContinuousModuleIsoOfLinearEquiv Λ (LinearEquiv.refl Λ (ULift.{u + 1} Λ))
      fun σ v => ?_)⟩
  have h1 : artinSchreierCharacter k A' (φ g) ψ y p₀' σ =
      artinSchreierCharacter k A g ψ (y.map f.hom) p₀ (etaleFundamentalGroupMap f.hom y σ) :=
    congrArg (fun χ => χ σ) hχ
  show ((artinSchreierCharacter k A g ψ (y.map f.hom) p₀
      (etaleFundamentalGroupMap f.hom y σ) : Λˣ) : Λ) • v =
    ((artinSchreierCharacter k A' (φ g) ψ y p₀' σ : Λˣ) : Λ) • v
  rw [h1]

end Stacks.ArtinSchreier

end
