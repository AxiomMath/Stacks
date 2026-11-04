module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalConnectionFunctoriality
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalConnectionIntegrable

/-!
# The canonical integrable connection of a crystal, on the ambient schemes of `Cris(X/S)`

The canonical integrable connection of [Stacks, Lemma 60.15.1, Tag 07J6] on the ambient scheme of
each object of `Cris(X/S)`, and its functoriality in the object.  A sheaf of `𝒪_{X/S}`-modules on
`Cris(X/S)` is the same thing as the family of its restrictions `F_T` to the ambient schemes of
the objects `(U, T, δ)` together with the transition maps along the morphisms of the site, and the
same holds of `F ⊗_{𝒪_{X/S}} Ω_{X/S}`, whose restriction to `T` is `F_T ⊗_{𝒪_T} Ω_{T/S,δ}`
([Stacks, Tag 07IZ] for `Ω_{X/S}`).  Throughout, `F` is a crystal (`...SmallSite.IsSheafCrystal`,
the crystal condition with the comparison maps of sheaves); no quasi-coherence is assumed.

The canonical connection `...SmallSite.crystalConnection` at an object `(U, T, δ)` of `Cris(X/S)`
is a morphism of sheaves of abelian groups `∇ : F_T ⟶ F_T ⊗_{𝒪_T} Ω_{T/S,δ}` on `T`.  On a
section `s` it is `∇(s) = p₁^* s - c(p₀^* s)` on the first-order universal thickening `T'` of
[Stacks, Tag 07J2], read in `F_T ⊗ Ω` through the identification
`F_T ⊗_{𝒪_T} Ω_{T/S,δ} ≅ ker(F_{T'} → F_T)`
(`...SmallSite.firstOrderTensorInclusion_crystalConnectionApp`), an isomorphism because `F` is a
crystal (`...SmallSite.isIso_firstOrderKernelComparison_of_isSheafCrystal`).

## Main results

* `...SmallSite.crystalConnection_isConnection` — **`∇` is a connection on `Cris(X/S)`**: the
  Leibniz rule `∇(f s) = f ∇(s) + s ⊗ d f` holds for all local sections, and `∇` commutes with
  the transition maps of `F` and of `F ⊗ Ω` along every morphism `g` of `Cris(X/S)`, the
  transition map of `F ⊗ Ω` being `x ⊗ ω ↦ g^* x ⊗ g^* ω` (and the only compatible family of
  additive maps with this property, `...SmallSite.eq_crystalTensorTransition`).
* `...SmallSite.crystalConnection_isIntegrable` — **`∇` is integrable**: with the degree-one
  extension `∇ : F_T ⊗ Ω ⟶ F_T ⊗ Ω²` of [Stacks, Section 60.15 / Remark 07I0], given by the
  rule `∇(x ⊗ ω) = ∇(x) ∧ ω + x ⊗ d ω` (and the only compatible family of additive maps given by
  that rule, `...SmallSite.eq_crystalConnectionExtensionApp`), the composite
  `F_T ⟶ F_T ⊗ Ω ⟶ F_T ⊗ Ω²` vanishes.

## References

* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J5](https://stacks.math.columbia.edu/tag/07J5)
* [Stacks Project, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07J3](https://stacks.math.columbia.edu/tag/07J3)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} {F : SheafOfModules.{u} (structureSheaf S)}

/-- **The canonical connection of a crystal of [Stacks, Tag 07J6], at the objects of
`Cris(X/S)`, satisfies the Leibniz rule and is functorial in the object.**
Let `F` be a crystal in `𝒪_{X/S}`-modules on `Cris(X/S)` and let
`∇ = ...SmallSite.crystalConnection` be its canonical connection
`F_T ⟶ F_T ⊗_{𝒪_T} Ω_{T/S,δ}` at the objects `(U, T, δ)` of `Cris(X/S)`.  Then

1. (**Leibniz rule**) for every object, every open `W` of its ambient scheme `T`, every function
   `f` and every section `s` of `F_T` over `W`, `∇(f s) = f ∇(s) + s ⊗ d f`, with
   `d = d_{T/S,δ}` the universal divided power derivation;
2. (**functoriality in `T`**) for every morphism `g : (U_B, T_B, δ_B) ⟶ (U_A, T_A, δ_A)` of
   `Cris(X/S)` and every open `W` of `T_A`, the transition map
   `τ_g : F_{T_A} ⊗ Ω_{T_A} ⟶ g_*(F_{T_B} ⊗ Ω_{T_B})` (`...SmallSite.crystalTensorTransition`) is
   `x ⊗ ω ↦ g^* x ⊗ g^* ω` on local pure tensors, and `τ_g ∘ ∇_A = ∇_B ∘ g^*`.

So `∇` is a map `F ⟶ F ⊗_{𝒪_{X/S}} Ω_{X/S}` of abelian sheaves on `Cris(X/S)` satisfying the
Leibniz rule: a connection in the sense of [Stacks, Section 60.15, Tag 07J5]. -/
theorem crystalConnection_isConnection (hF : IsSheafCrystal F) :
    (∀ (A : CrystallineThickening S) (W : A.obj.thickening.target.scheme.Opens)
        (f : ↑(A.obj.thickening.target.scheme.ringCatSheaf.obj.obj (op W)))
        (s : (crysAmbientSchemeModules F A).val.obj (op W)),
      crystalConnectionApp A hF W (f • s) =
        f • crystalConnectionApp A hF W s +
          firstOrderTensorTmul F A W s
            (sheafApp A.obj.thickening.target S.S.scheme A.obj.toBase.hom W f)) ∧
    (∀ {A B : CrystallineThickening S} (g : B ⟶ A)
        (W : A.obj.thickening.target.scheme.Opens),
      (∀ (x : (crysAmbientSchemeModules F A).val.obj (op W))
          (ω : (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme
            A.obj.toBase.hom).val.obj (op W)),
        crystalTensorTransition g hF W (firstOrderTensorTmul F A W x ω) =
          firstOrderTensorTmul F B (g.hom.targetHom.hom ⁻¹ᵁ W)
            (crystalRestrict F (CrystallineThickening.restrictOpenMap g W) x)
            ((dpDifferentialsMapSheaf g.hom).app W ω)) ∧
      ∀ s : (crysAmbientSchemeModules F A).val.obj (op W),
        crystalTensorTransition g hF W (crystalConnectionApp A hF W s) =
          crystalConnectionApp B hF (g.hom.targetHom.hom ⁻¹ᵁ W)
            (crystalRestrict F (CrystallineThickening.restrictOpenMap g W) s)) :=
  ⟨fun A W f s ↦ crystalConnectionApp_smul A hF W f s,
    fun g W ↦ ⟨fun x ω ↦ crystalTensorTransition_tmul g hF W x ω,
      fun s ↦ crystalTensorTransition_crystalConnectionApp g hF W s⟩⟩

/-- **The canonical connection of a crystal of [Stacks, Tag 07J6], at an object of `Cris(X/S)`, is
integrable.**  Let `F` be a crystal in `𝒪_{X/S}`-modules on `Cris(X/S)` and `(U, T, δ)` an object
of `Cris(X/S)`.  The degree-one extension
`∇ = ...SmallSite.crystalConnectionExtension : F_T ⊗_{𝒪_T} Ω_{T/S,δ} ⟶ F_T ⊗_{𝒪_T} Ω²_{T/S,δ}`
of the canonical connection is given by the rule of [Stacks, Remark 07I0],
`∇(x ⊗ ω) = ∇(x) ∧ ω + x ⊗ d ω` on local pure tensors (which determines it,
`...SmallSite.eq_crystalConnectionExtensionApp`), and the composite

`F_T ⟶ F_T ⊗_{𝒪_T} Ω_{T/S,δ} ⟶ F_T ⊗_{𝒪_T} Ω²_{T/S,δ}`

is zero: the connection is integrable in the sense of [Stacks, Section 60.15, Tag 07J5]. -/
theorem crystalConnection_isIntegrable (hF : IsSheafCrystal F) (A : CrystallineThickening S) :
    (∀ (W : A.obj.thickening.target.scheme.Opens)
        (x : (crysAmbientSchemeModules F A).val.obj (op W))
        (ω : (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme
          A.obj.toBase.hom).val.obj (op W)),
      crystalConnectionExtensionApp A hF W (firstOrderTensorTmul F A W x ω) =
        crystalWedge F A W (crystalConnectionApp A hF W x) ω +
          secondOrderTensorTmul F A W x
            (dpDeRham A.obj.thickening.target S.S.scheme A.obj.toBase.hom (op W) ω)) ∧
    crystalConnection A hF ≫ crystalConnectionExtension A hF = 0 :=
  ⟨fun W x ω ↦ crystalConnectionExtensionApp_tmul A hF W x ω,
    crystalConnection_comp_crystalConnectionExtension A hF⟩

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
