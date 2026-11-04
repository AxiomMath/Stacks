module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartRatioPullbackLocalMulBridge
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTripleFunctorLaws

/-!
# Pulling a section over an open back along a composite

`AlgebraicGeometry.pullbackSectionHom f M U V h` reads a section of `M` over an open `U` of the
target as a section of `f^*M` over an open `V ⊆ f^{-1}(U)` of the source.  The composition law for
it — pulling back along `g` and then along `f` is pulling back along `f ≫ g`, up to the
composition law `f^*g^* ≅ (f ≫ g)^*` of the inverse image — is available as
`Stacks.AlgebraicGeometry.ProjTripleFunctorLaws.pullbackSectionHom_comp`, but **only for a global
section**: its `U` is `⊤`.

Clause (3) of [Stacks, Tag 01O9] compares the [Stacks, Tag 01NK] datum induced by a global
`(ℒ, ψ)` over two nested opens `Z ≤ V` of the base.  The sections it must compare are the values
`ψ(a) ∈ Γ(f^{-1}(V), ℒ^{⊗ n})`, which live over `f^{-1}(V)` and are **not** global on the total
space; the composite being pulled along is the inclusion `f^{-1}(Z) ↪ f^{-1}(V) ↪ X`.  So the
composition law is needed with its source open arbitrary, and that is what this file proves.

## Main results

* `…ProjChartRatioPullbackLocalMul.pullbackSectionHom_congr`: pulling a section back along equal
  morphisms agrees, through `AlgebraicGeometry.Scheme.Modules.pullbackCongr`.
* `…ProjChartRatioPullbackLocalMul.pullbackSectionHom_comp_of_le`: **the composition law for an
  arbitrary source open.**  For `f : X₂ ⟶ X₁`, `g : X₁ ⟶ X₀`, a section of `M` over an open `U` of
  `X₀` whose preimage in `X₁` is everything, pulling back along `g` and then along `f` is pulling
  back along `f ≫ g`, read through the composition law of the inverse image.

## Implementation notes

The proof is that of the global case with the global section replaced by a section over `U`, which costs
two things.  The naturality of the adjunction unit **in the open**,
`Stacks.RingedSpace.pullbackUnit_restrict`, is needed to move the restriction from `g^{-1}(U)` to
`⊤` past the second unit; and the two restriction maps that result have to be composed into the
single one the statement names, which is
`PresheafOfModules.map_comp_apply` followed by
`PresheafOfModules.congr_map_apply` at `Subsingleton.elim` — the opens of a scheme form a poset,
so any two inclusions with the same endpoints are the same morphism.  That is the ending of
`AlgebraicGeometry.pullbackSectionHom_map`'s own proof.

Both the unit cocycle `Stacks.PullbackTensorCoherence.pullbackCompIso_app_inv_pullbackUnit` and
`pullbackUnit_restrict` are stated at the ringed-space spelling of the inverse image, and
`AlgebraicGeometry.Scheme.Modules` does not unfold at the transparency the rewriting tactics check
their motives at.  Each is therefore re-ascribed by a `have` at the scheme spelling, where the
bridge is `rfl`, before being used — the discipline
`StacksFrontier.AlgebraicGeometry.Constructions.ProjChartPullbackCotensorator` records for the
same reason.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.TensorSheafSpellingIso (pullbackCompIso)
open Stacks.RingedSpace (pullbackUnit pullbackUnit_restrict)

universe u

namespace Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul

variable {X₀ X₁ X₂ : Scheme.{u}} (f : X₂ ⟶ X₁) (g : X₁ ⟶ X₀) (M : X₀.Modules) (U : X₀.Opens)

/-- **Pulling a section back along equal morphisms agrees**, through the transport
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` of the inverse image along an equality of
morphisms.  Used to replace the inclusion of a smaller open by the composite of the inclusion in
an intermediate open with that one's inclusion. -/
public theorem pullbackSectionHom_congr {g g' : X₁ ⟶ X₀} (e : g = g') (V : X₁.Opens)
    (h : V ≤ g ⁻¹ᵁ U) (x : Γ(M, U)) :
    pullbackSectionHom g' M U V (by rw [← e]; exact h) x
      = Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr e).hom.app M) V
          (pullbackSectionHom g M U V h x) := by
  subst e
  rfl

/-- **The composition law for pulling a section over an arbitrary open back along a composite.**
For a section `x` of `M` over an open `U` of `X₀` whose preimage in `X₁` is everything, pulling
`x` back to `X₁` and then to `X₂` is pulling it back along `f ≫ g`, read through the composition
law `f^*g^* ≅ (f ≫ g)^*`.

`Stacks.AlgebraicGeometry.ProjTripleFunctorLaws.pullbackSectionHom_comp` is the case `U = ⊤`;
clause (3) of [Stacks, Tag 01O9] needs the general one, the sections it compares being the values
of `ψ` over the preimage of an open of the base. -/
public theorem pullbackSectionHom_comp_of_le (h₁ : (⊤ : X₁.Opens) ≤ g ⁻¹ᵁ U)
    (h₂ : (⊤ : X₂.Opens) ≤ (f ≫ g) ⁻¹ᵁ U) (x : Γ(M, U)) :
    pullbackSectionHom f ((Scheme.Modules.pullback g).obj M) ⊤ ⊤ (by simp)
        (pullbackSectionHom g M U ⊤ h₁ x)
      = Scheme.Modules.Hom.app ((pullbackCompIso f g).inv.app M) ⊤
          (pullbackSectionHom (f ≫ g) M U ⊤ h₂ x) := by
  have key := Stacks.PullbackTensorCoherence.pullbackCompIso_app_inv_pullbackUnit
      f.toLRSHom.toShHom g.toLRSHom.toShHom M (op U) x
  have hres := pullbackUnit_restrict f.toLRSHom.toShHom
      ((Scheme.Modules.pullback g).obj M) (homOfLE h₁).op
      (pullbackUnit g.toLRSHom.toShHom M (op U) x)
  have hnat : ∀ z : Γ((Scheme.Modules.pullback (f ≫ g)).obj M, (f ≫ g) ⁻¹ᵁ U),
      Scheme.Modules.Hom.app ((pullbackCompIso f g).inv.app M) ⊤
          (((Scheme.Modules.pullback (f ≫ g)).obj M).presheaf.map (homOfLE h₂).op z)
        = ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M)).presheaf.map
            (homOfLE h₂).op
            (Scheme.Modules.Hom.app ((pullbackCompIso f g).inv.app M) ((f ≫ g) ⁻¹ᵁ U) z) :=
    fun z => congrFun (congrArg (fun φ => φ.hom)
      (((pullbackCompIso f g).inv.app M).val.naturality (homOfLE h₂).op)) z
  have hL : pullbackSectionHom f ((Scheme.Modules.pullback g).obj M) ⊤ ⊤ (by simp)
        (pullbackSectionHom g M U ⊤ h₁ x)
      = ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M)).presheaf.map
          (homOfLE (by simp : (⊤ : X₂.Opens) ≤ f ⁻¹ᵁ ⊤)).op
          (pullbackUnit f.toLRSHom.toShHom ((Scheme.Modules.pullback g).obj M) (op ⊤)
            (((Scheme.Modules.pullback g).obj M).presheaf.map (homOfLE h₁).op
              (pullbackUnit g.toLRSHom.toShHom M (op U) x))) := rfl
  have hres' : ((Scheme.Modules.pullback f).obj
          ((Scheme.Modules.pullback g).obj M)).presheaf.map
        ((RingedSpaceModuleAdjunction.opensMap f.toLRSHom.toShHom).op.map (homOfLE h₁).op)
        (pullbackUnit f.toLRSHom.toShHom ((Scheme.Modules.pullback g).obj M) (op (g ⁻¹ᵁ U))
          (pullbackUnit g.toLRSHom.toShHom M (op U) x))
      = pullbackUnit f.toLRSHom.toShHom ((Scheme.Modules.pullback g).obj M) (op ⊤)
          (((Scheme.Modules.pullback g).obj M).presheaf.map (homOfLE h₁).op
            (pullbackUnit g.toLRSHom.toShHom M (op U) x)) := hres
  have key' : Scheme.Modules.Hom.app ((pullbackCompIso f g).inv.app M) ((f ≫ g) ⁻¹ᵁ U)
        (pullbackUnit (f ≫ g).toLRSHom.toShHom M (op U) x)
      = pullbackUnit f.toLRSHom.toShHom ((Scheme.Modules.pullback g).obj M) (op (g ⁻¹ᵁ U))
          (pullbackUnit g.toLRSHom.toShHom M (op U) x) := key
  refine Eq.trans (hL.trans ?_) (hnat _).symm
  refine Eq.trans (congrArg _ hres'.symm) ?_
  refine Eq.trans (congrArg _ (congrArg _ key'.symm)) ?_
  exact (PresheafOfModules.map_comp_apply _ _ _ _).symm.trans
    (PresheafOfModules.congr_map_apply _ (Subsingleton.elim _ _) _)

end Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul

end
