module

public import StacksFrontier.Topology.Sheaves.Sheafify.LocallyConstant
public import StacksFrontier.Topology.Sheaves.Stalk.Constant

/-!
# Stalks of the constant sheaf of locally constant functions

Fix a topological space `X`, a set `A` and a point `x ∈ X`. Stacks 006W defines the constant
sheaf `A̲` as the sheaf of locally constant maps `U → A`, and Stacks 007B asserts that the
canonical map `c : A_p → A̲` from the constant presheaf, sending `a` to the constant function
`a`, induces canonical bijections `A = (A_p)_x = A̲_x`.

`TopCat.locallyConstantSheaf` is `A̲`, the subsheaf of all functions cut out by the local
predicate `TopCat.isLocallyConstantLocal`, and `TopCat.constantPresheafToLocallyConstant` is `c`
(both from `StacksFrontier.Topology.Sheaves.Sheafify.LocallyConstant`, where Stacks 0081 is
proved). Stacks 007B is `alphaX_bijective_and_locallyConstantStalkMap_bijective`, with the
composite `A = A̲_x` in `locallyConstantStalkMap_comp_alphaX_bijective`. The key input is
`stalkToFiber_isLocallyConstantLocal_injective`: the germ at `x` of a locally constant function
is determined by its value at `x`, since two locally constant functions agreeing at `x` agree on
a neighbourhood of `x`.

## References

* [Stacks Project, Tag 006W](https://stacks.math.columbia.edu/tag/006W)
* [Stacks Project, Tag 007B](https://stacks.math.columbia.edu/tag/007B)
-/

@[expose] public section

open TopCat CategoryTheory Opposite TopologicalSpace

universe u

variable (X : TopCat.{u}) (A : Type u) (x : X)

/-- The map on stalks `c_x : (A_p)_x → A̲_x` induced by functoriality of stalks from
`c = TopCat.constantPresheafToLocallyConstant`. -/
noncomputable def locallyConstantStalkMap :
    (constPresheaf X A).stalk x ⟶ (locallyConstantSheaf X A).presheaf.stalk x :=
  (TopCat.Presheaf.stalkFunctor (Type u) x).map (constantPresheafToLocallyConstant X A)

/-- Evaluating at `x` the germ `c_x (α_x a)` of the constant function with value `a` gives
back `a`. -/
theorem stalkToFiber_locallyConstantStalkMap_alphaX (a : A) :
    stalkToFiber (isLocallyConstantLocal X A) x
      (locallyConstantStalkMap X A x (alphaX X A x a)) = a := by
  have h : locallyConstantStalkMap X A x (alphaX X A x a) =
      (locallyConstantSheaf X A).presheaf.germ ⊤ x trivial
        ((constantPresheafToLocallyConstant X A).app (op ⊤) a) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x trivial
      (constantPresheafToLocallyConstant X A) a
  rw [h]
  exact stalkToFiber_germ (isLocallyConstantLocal X A) ⊤ x trivial _

/-- Two locally constant functions defined near `x` with the same value at `x` agree on a
neighbourhood of `x`; hence evaluation at `x` is injective on the stalk `A̲_x`. -/
theorem stalkToFiber_isLocallyConstantLocal_injective :
    Function.Injective (stalkToFiber (isLocallyConstantLocal X A) x) := by
  apply stalkToFiber_injective
  intro U V fU hU fV hV e
  let S : Set X := Subtype.val '' {y | fU y = fU ⟨x, U.2⟩} ∩
    Subtype.val '' {y | fV y = fV ⟨x, V.2⟩}
  have hS : IsOpen S :=
    (U.1.isOpen.isOpenMap_subtype_val _ ((hU : IsLocallyConstant fU).isOpen_fiber _)).inter
      (V.1.isOpen.isOpenMap_subtype_val _ ((hV : IsLocallyConstant fV).isOpen_fiber _))
  have hxS : x ∈ S := ⟨⟨⟨x, U.2⟩, rfl, rfl⟩, ⟨⟨x, V.2⟩, rfl, rfl⟩⟩
  have hSU : S ⊆ U.1 := fun y hy => by
    obtain ⟨z, -, rfl⟩ := hy.1
    exact z.2
  have hSV : S ⊆ V.1 := fun y hy => by
    obtain ⟨z, -, rfl⟩ := hy.2
    exact z.2
  refine ⟨⟨⟨S, hS⟩, hxS⟩, homOfLE hSU, homOfLE hSV, fun w => ?_⟩
  obtain ⟨⟨z₁, hz₁, hz₁w⟩, ⟨z₂, hz₂, hz₂w⟩⟩ := w.2
  change fU ⟨w.1, hSU w.2⟩ = fV ⟨w.1, hSV w.2⟩
  have h₁ : (⟨w.1, hSU w.2⟩ : U.1) = z₁ := Subtype.ext hz₁w.symm
  have h₂ : (⟨w.1, hSV w.2⟩ : V.1) = z₂ := Subtype.ext hz₂w.symm
  rw [h₁, h₂]
  exact (hz₁ : fU z₁ = _).trans (e.trans (hz₂ : fV z₂ = _).symm)

/-- The canonical bijection `A = A̲_x` of Stacks 007B, for `A̲` the sheaf of locally constant
functions of Stacks 006W: the composite `A → (A_p)_x → A̲_x`, `a ↦` the germ at `x` of the
constant function `a`, is bijective. Its inverse is evaluation at `x`; injectivity of the
evaluation is the statement that a germ of a locally constant function at `x` is determined by
its value at `x`. -/
@[stacks 007B "`A̲` is the sheaf of locally constant functions of 006W; this is `A = A̲_x`"]
theorem locallyConstantStalkMap_comp_alphaX_bijective :
    Function.Bijective (fun a => locallyConstantStalkMap X A x (alphaX X A x a)) := by
  have hl : Function.LeftInverse (stalkToFiber (isLocallyConstantLocal X A) x)
      (fun a => locallyConstantStalkMap X A x (alphaX X A x a)) :=
    stalkToFiber_locallyConstantStalkMap_alphaX X A x
  refine ⟨hl.injective, fun z => ⟨stalkToFiber (isLocallyConstantLocal X A) x z, ?_⟩⟩
  apply stalkToFiber_isLocallyConstantLocal_injective X A x
  exact hl _

/-- **Stacks 007B**, for the constant sheaf `A̲` of Stacks 006W (locally constant functions):
the canonical maps `α_x : A → (A_p)_x` and `c_x : (A_p)_x → A̲_x`, the second induced by
functoriality of stalks from `c : A_p → A̲`, `a ↦` the constant function `a`, are bijections,
giving the canonical bijections `A = (A_p)_x = A̲_x`. -/
@[stacks 007B "`A̲` is the sheaf of locally constant functions of 006W"]
theorem alphaX_bijective_and_locallyConstantStalkMap_bijective :
    Function.Bijective (alphaX X A x) ∧ Function.Bijective (locallyConstantStalkMap X A x) := by
  refine ⟨alphaX_bijective X A x, ?_⟩
  have hα := alphaX_bijective X A x
  have hβ := locallyConstantStalkMap_comp_alphaX_bijective X A x
  refine ⟨fun s t hst => ?_, fun z => ?_⟩
  · obtain ⟨a, rfl⟩ := hα.2 s
    obtain ⟨b, rfl⟩ := hα.2 t
    exact congrArg (alphaX X A x) (hβ.1 hst)
  · obtain ⟨a, ha⟩ := hβ.2 z
    exact ⟨alphaX X A x a, ha⟩
