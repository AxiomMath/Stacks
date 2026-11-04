module

public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.TensorHomAdjunction
import StacksCore.Tactic.StacksAttribute

/-!
# Currying for internal Hom complexes of modules on a ringed site

Let `(C, O)` be a ringed site and let `K`, `L`, `M` be cochain complexes of `O`-modules.
Currying identifies the iterated internal Hom complex `SheafHom•(K, SheafHom•(L, M))` with the
internal Hom complex `SheafHom•(Tot(K ⊗_O L), M)` out of the total tensor complex, and the
identification is functorial in all three complexes. This is [Stacks, Tag 0A90].

Here `SheafHom•(K, L)` is `(ihom K).obj L` for the closed structure on `Comp(Mod(O))` coming from
the sheafified tensor product; in degree `n` it is the product over `p` of the internal Hom
sheaves `SheafHom(K^p, L^(p + n))` (`Stacks.Cohomology.SheafHomComplexCurrying.sheafHomComplex_X`).
The ringed site is a `RingedSite.{u, v, max u v}`, with modules in `SheafOfModules.{max u v}`.

## Main definitions

* `AlgebraicGeometry.RingedSite.sheafHomTensorIso`: the currying isomorphism
  `SheafHom•(K, SheafHom•(L, M)) ≅ SheafHom•(Tot(K ⊗_O L), M)`.
* `AlgebraicGeometry.RingedSite.SheafHomTensorIsoConstruction`: the currying isomorphism together
  with the induced maps of internal Hom complexes, their value on a pair of identities and their
  simultaneous functoriality, as a single datum.
* `AlgebraicGeometry.RingedSite.sheafHomTensorIsoConstruction`: that datum for a ringed site.

## Main results

* `CategoryTheory.MonoidalClosed.ihomMap_id`: the map of internal homs induced by a pair of
  identities is the identity.
* `AlgebraicGeometry.RingedSite.sheafHomComplexMap_id`: the induced map of internal Hom complexes
  along a pair of identities is the identity.
* `AlgebraicGeometry.RingedSite.sheafHomTensorIso_natural`: the currying isomorphism is natural
  simultaneously in all three complexes.

## References

* [The Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [The Stacks Project, Tag 0A8M](https://stacks.math.columbia.edu/tag/0A8M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry

noncomputable section

universe u v

namespace CategoryTheory.MonoidalClosed

variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [MonoidalClosed D]

/-- The map of internal homs induced by a pair of identities is the identity. -/
@[simp] lemma ihomMap_id (A B : D) : ihomMap (𝟙 A) (𝟙 B) = 𝟙 ((ihom A).obj B) := by
  simp [ihomMap, pre_id]

end CategoryTheory.MonoidalClosed

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, max u v})

/-- The total complexes of the tensor double complexes of complexes of `O`-modules exist. -/
local instance hasMapBifunctor :
    letI := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, v, max u v, max u v, max u v}
      X.O
    ∀ K L :
      CochainComplex (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} X.O)
        (ComplexShape.up ℤ) :=
  Stacks.Cohomology.SheafHomComplexCurrying.hasMapBifunctor X.O

/-- The map `SheafHom•(K, M) ⟶ SheafHom•(K', M')` induced by a pair of identities is the
identity. -/
@[simp] lemma sheafHomComplexMap_id
    (K M :
      CochainComplex (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    Stacks.Cohomology.SheafHomComplexCurrying.sheafHomComplexMap X.O (𝟙 K) (𝟙 M) =
      𝟙 (Stacks.Cohomology.SheafHomComplexCurrying.sheafHomComplex X.O K M) := by
  simp [Stacks.Cohomology.SheafHomComplexCurrying.sheafHomComplexMap]

/-- **Stacks 0A90.** The canonical isomorphism
`SheafHom•(K, SheafHom•(L, M)) ≅ SheafHom•(Tot(K ⊗_O L), M)` for complexes of `O`-modules on a
ringed site. -/
def sheafHomTensorIso
    (K L M :
      CochainComplex (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    Stacks.Cohomology.SheafHomComplexCurrying.sheafHomComplex X.O K
      (Stacks.Cohomology.SheafHomComplexCurrying.sheafHomComplex X.O L M) ≅
      Stacks.Cohomology.SheafHomComplexCurrying.sheafHomComplex X.O
        (Stacks.Cohomology.SheafHomComplexCurrying.tensorComplex X.O K L) M :=
  Stacks.Cohomology.SheafHomComplexCurrying.sheafHomTensorIso X.O K L M

/-- **Stacks 0A90, functoriality.** The currying isomorphism is natural simultaneously in all
three complexes. -/
theorem sheafHomTensorIso_natural
    {K K' L L' M M' :
      CochainComplex (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (k : K' ⟶ K) (l : L' ⟶ L) (m : M ⟶ M') :
    letI := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, v, max u v, max u v, max u v}
      X.O
    Stacks.Cohomology.SheafHomComplexCurrying.sheafHomComplexMap X.O k
      (Stacks.Cohomology.SheafHomComplexCurrying.sheafHomComplexMap X.O l m) ≫
        (sheafHomTensorIso X K' L' M').hom =
      (sheafHomTensorIso X K L M).hom ≫
        Stacks.Cohomology.SheafHomComplexCurrying.sheafHomComplexMap X.O
          (((Stacks.SheafOfModules.Tensor.tensorComplex.{u, v, max u v} X.O).map k).app L' ≫
            ((Stacks.SheafOfModules.Tensor.tensorComplex.{u, v, max u v} X.O).obj K).map l) m :=
  have := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, v, max u v, max u v, max u v}
    X.O
  Stacks.Cohomology.SheafHomComplexCurrying.sheafHomTensorIso_natural X.O k l m

/-- The currying isomorphism of Tag 0A90, together with the induced maps of internal Hom
complexes, their value on a pair of identities, and their simultaneous functoriality. -/
structure SheafHomTensorIsoConstruction where
  /-- The map of internal Hom complexes induced by maps in both variables. -/
  homMap : {K K' M M' :
      CochainComplex (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ} →
    (K' ⟶ K) → (M ⟶ M') →
      (Stacks.Cohomology.SheafHomComplexCurrying.sheafHomComplex X.O K M ⟶
        Stacks.Cohomology.SheafHomComplexCurrying.sheafHomComplex X.O K' M')
  /-- The identity maps induce an identity on internal Hom. -/
  homMap_id : ∀ K M :
      CochainComplex (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
    homMap (𝟙 K) (𝟙 M) = 𝟙 (Stacks.Cohomology.SheafHomComplexCurrying.sheafHomComplex X.O K M)
  /-- The canonical currying isomorphism. -/
  iso (K L M :
      CochainComplex (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    Stacks.Cohomology.SheafHomComplexCurrying.sheafHomComplex X.O K
      (Stacks.Cohomology.SheafHomComplexCurrying.sheafHomComplex X.O L M) ≅
      Stacks.Cohomology.SheafHomComplexCurrying.sheafHomComplex X.O
        (Stacks.Cohomology.SheafHomComplexCurrying.tensorComplex X.O K L) M
  /-- Currying commutes with maps in all three variables. -/
  natural :
    letI := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, v, max u v, max u v, max u v}
      X.O
    ∀ {K K' L L' M M' :
      CochainComplex (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
      (k : K' ⟶ K) (l : L' ⟶ L) (m : M ⟶ M'),
    homMap k (homMap l m) ≫ (iso K' L' M').hom =
      (iso K L M).hom ≫
        homMap (((Stacks.SheafOfModules.Tensor.tensorComplex.{u, v, max u v} X.O).map k).app L' ≫
          ((Stacks.SheafOfModules.Tensor.tensorComplex.{u, v, max u v} X.O).obj K).map l) m

/-- For complexes `K`, `L`, `M` of `O`-modules on a ringed site `(C, O)` there is an isomorphism
`SheafHom•(K, SheafHom•(L, M)) ≅ SheafHom•(Tot(K ⊗_O L), M)` of complexes of `O`-modules,
functorial in `K`, `L` and `M`. -/
@[stacks 0A90]
def sheafHomTensorIsoConstruction : SheafHomTensorIsoConstruction X where
  homMap k m := Stacks.Cohomology.SheafHomComplexCurrying.sheafHomComplexMap X.O k m
  homMap_id K M := sheafHomComplexMap_id X K M
  iso K L M := sheafHomTensorIso X K L M
  natural k l m := sheafHomTensorIso_natural X k l m

end AlgebraicGeometry.RingedSite

end

end
