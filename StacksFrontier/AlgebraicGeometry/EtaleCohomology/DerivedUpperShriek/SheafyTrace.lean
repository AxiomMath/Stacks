module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek.Compactification
import StacksCore.Tactic.StacksAttribute

/-!
# The sheafy trace map `Rf_*RHom(L, Rf^!K) ⟶ RHom(Rf_!L, K)`

Let `f : X ⟶ Y` be a separated morphism of finite type between quasi-compact and
quasi-separated schemes, let `Λ` be a torsion coefficient ring and let `Rf^!` be the right
adjoint of `Rf_!` of [Stacks, Tag 0G2C]. For `L` in `D(X_étale, Λ)` and `K` in
`D(Y_étale, Λ)` there is a canonical map

`Rf_*RHom_Λ(L, Rf^!K) ⟶ RHom_Λ(Rf_!L, K)`,

[Stacks, Tag 0GLB] (equation `more-etale-equation-sheafy-trace`). It is the composite

`Rf_*RHom_Λ(L, Rf^!K) ⟶ RHom_Λ(Rf_!L, Rf_!Rf^!K) ⟶ RHom_Λ(Rf_!L, K)`

of the canonical map of [Stacks, Tag 0GL7] with the internal Hom of the counit
`Rf_!Rf^!K ⟶ K` of the adjunction.

## Main definitions

* `Stacks.EtaleCohomology.DerivedUpperShriek.CompactificationData.sheafyTrace` — **the map of
  [Stacks, Tag 0GLB]**.

## Main results

* `CompactificationData.sheafyTrace_eq` — the defining composite.
* `CompactificationData.sheafyTrace_naturality_target` and
  `CompactificationData.sheafyTrace_naturality_source` — the map is covariant in `K` and
  contravariant in `L`.

## Implementation notes

The construction is formal: the only inputs are the map `α` of [Stacks, Tag 0GL7], built in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek.Compactification`, and an
adjunction `Rf_! ⊣ Rf^!`. The right adjoint is taken as data together with the adjunction
rather than extracted from the existence statement of [Stacks, Tag 0G2C]: the counit is what
the construction uses, and a right adjoint chosen from an existence statement carries no
counit. Any two right adjoints are canonically isomorphic, so nothing is lost.

`Rf_*` and `Rf_!` are the composites `Rf̄_*Rj_*` and `Rf̄_*j_!` of the chosen compactification,
exactly as in [Stacks, Tag 0GL7]; see the implementation notes there.

## References

* [Stacks Project, Tag 0GLB](https://stacks.math.columbia.edu/tag/0GLB)
* [Stacks Project, Tag 0GLA](https://stacks.math.columbia.edu/tag/0GLA)
* [Stacks Project, Tag 0GL7](https://stacks.math.columbia.edu/tag/0GL7)
* [Stacks Project, Tag 0G2C](https://stacks.math.columbia.edu/tag/0G2C)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace Stacks.EtaleCohomology.DerivedUpperShriek.CompactificationData

universe v₁ u₁ v₂ u₂ v₃ u₃

variable {DU : Type u₁} [Category.{v₁} DU] {DX : Type u₂} [Category.{v₂} DX]
  {DY : Type u₃} [Category.{v₃} DY] (data : CompactificationData DU DX DY)
  {upperShriek : DY ⥤ DU} (adj : data.derivedLowerShriek ⊣ upperShriek)

/-- The sheafy trace map

`Rf_*RHom_Λ(L, Rf^!K) ⟶ RHom_Λ(Rf_!L, K)`,

the composite of the canonical map `α` of [Stacks, Tag 0GL7] at `(L, Rf^!K)` with the internal
Hom of the counit `Rf_!Rf^!K ⟶ K` of the adjunction `Rf_! ⊣ Rf^!`. -/
@[stacks 0GLB "the map, for a chosen compactification and a chosen adjunction Rf_! ⊣ Rf^!"]
def sheafyTrace (L : DU) (K : DY) :
    data.derivedPushforward.obj ((data.homU.obj (op L)).obj (upperShriek.obj K)) ⟶
      (data.homY.obj (op (data.derivedLowerShriek.obj L))).obj K :=
  data.lowerShriekHomMap L (upperShriek.obj K) ≫
    (data.homY.obj (op (data.derivedLowerShriek.obj L))).map (adj.counit.app K)

/-- The sheafy trace map is the canonical map of [Stacks, Tag 0GL7] followed by the internal Hom
of the counit of `Rf_! ⊣ Rf^!`. -/
@[stacks 0GLB "the defining composite through RHom(Rf_!L, Rf_!Rf^!K)"]
theorem sheafyTrace_eq (L : DU) (K : DY) :
    sheafyTrace data adj L K =
      data.lowerShriekHomMap L (upperShriek.obj K) ≫
        (data.homY.obj (op (data.derivedLowerShriek.obj L))).map (adj.counit.app K) :=
  rfl

/-- The sheafy trace map is natural in `K`. -/
@[stacks 0GLB "functoriality in K"]
theorem sheafyTrace_naturality_target (L : DU) {K K' : DY} (k : K ⟶ K') :
    data.derivedPushforward.map ((data.homU.obj (op L)).map (upperShriek.map k)) ≫
        sheafyTrace data adj L K' =
      sheafyTrace data adj L K ≫
        (data.homY.obj (op (data.derivedLowerShriek.obj L))).map k := by
  have hc : data.derivedLowerShriek.map (upperShriek.map k) ≫ adj.counit.app K' =
      adj.counit.app K ≫ k := adj.counit.naturality k
  rw [sheafyTrace_eq, sheafyTrace_eq, ← Category.assoc,
    data.lowerShriekHomMap_naturality_target L (upperShriek.map k), Category.assoc,
    Category.assoc, ← Functor.map_comp, hc, Functor.map_comp]

/-- The sheafy trace map is natural in `L`, contravariantly. -/
@[stacks 0GLB "functoriality in L"]
theorem sheafyTrace_naturality_source {L L' : DU} (l : L' ⟶ L) (K : DY) :
    data.derivedPushforward.map ((data.homU.map l.op).app (upperShriek.obj K)) ≫
        sheafyTrace data adj L' K =
      sheafyTrace data adj L K ≫
        (data.homY.map (data.derivedLowerShriek.map l).op).app K := by
  have hH : (data.homY.obj (op (data.derivedLowerShriek.obj L))).map (adj.counit.app K) ≫
        (data.homY.map (data.derivedLowerShriek.map l).op).app K =
      (data.homY.map (data.derivedLowerShriek.map l).op).app
          (data.derivedLowerShriek.obj (upperShriek.obj K)) ≫
        (data.homY.obj (op (data.derivedLowerShriek.obj L'))).map (adj.counit.app K) :=
    (data.homY.map (data.derivedLowerShriek.map l).op).naturality (adj.counit.app K)
  rw [sheafyTrace_eq, sheafyTrace_eq, ← Category.assoc,
    data.lowerShriekHomMap_naturality_source l (upperShriek.obj K), Category.assoc,
    Category.assoc, ← hH]

end Stacks.EtaleCohomology.DerivedUpperShriek.CompactificationData

end
