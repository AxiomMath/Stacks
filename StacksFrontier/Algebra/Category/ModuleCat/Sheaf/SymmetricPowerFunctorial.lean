module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricAlgebras
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Functoriality of the symmetric power of a sheaf of modules in its module argument

Let `(C, J)` be a site, `O♯` a sheaf of commutative rings on it and `M`, `N` sheaves of modules
over the underlying sheaf of rings. A morphism `f : M ⟶ N` induces a morphism
`Symⁿ f : Symⁿ M ⟶ Symⁿ N` on symmetric powers, compatibly with identities and composition. It
is the degree-`n` component of the unique unital homomorphism of sheaves of graded algebras
`Sym(M) ⟶ Sym(N)` extending `f`.

## Main definitions

* `SheafOfModules.GradedAlgebra.IsSymmetricAlgebra.map`: the unital homomorphism of sheaves of
  graded algebras `Sym(M) ⟶ Sym(N)` induced by a morphism `M ⟶ N`, and
  `IsSymmetricAlgebra.pieceMap` its degree-`n` component.
* `SheafOfModules.GradedAlgebra.IsSymmetricAlgebra.pieceIsoOfIso`: the degreewise isomorphism
  induced by an isomorphism of sheaves of modules.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.symmetricPowerMap`: the induced map on the
  degree-`n` symmetric powers of two `TensorExteriorSymmetricAlgebras` packages, and
  `symmetricSquareMap` its degree-two case.

## Main results

* `SheafOfModules.GradedAlgebra.IsSymmetricAlgebra.map_app_one`: the induced homomorphism extends
  `f`.
* `SheafOfModules.GradedAlgebra.IsSymmetricAlgebra.map_id` and `map_comp`, and their degreewise
  forms `pieceMap_id` and `pieceMap_comp`: functoriality.
* `SheafOfModules.GradedAlgebra.IsSymmetricAlgebra.isIso_pieceMap`: the map induced by an
  isomorphism is an isomorphism in every degree.
* `SheafOfModules.GradedAlgebra.IsSymmetricAlgebra.isSplitMono_pieceMap` and
  `mono_pieceMap_of_retraction`: a morphism with a retraction induces a split monomorphism on
  every symmetric power.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory

universe t a v₁ u₁ v u w

namespace SheafOfModules.GradedAlgebra

section Site

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {M N P : SheafOfModules.{a} R} {A B D : GradedAlgebra.{t, a} R} {ι : M ⟶ A.piece 1}
  {κ : N ⟶ B.piece 1} {lam : P ⟶ D.piece 1}

namespace IsSymmetricAlgebra

/-- The homomorphism of symmetric algebras induced by a morphism of sheaves of modules: given
symmetric algebras `A` of `M` and `B` of `N` and a morphism `f : M ⟶ N`, the unique unital
homomorphism `A ⟶ B` of sheaves of graded algebras extending `f`. -/
@[ega "II 1.7.4" "more general", ega "II 4.1.2" "more general"]
noncomputable def map (hA : IsSymmetricAlgebra A ι) (hB : IsSymmetricAlgebra B κ) (f : M ⟶ N) :
    UnitalHom A B :=
  hA.isUniversal.desc B (f ≫ κ) (pairwiseCommutes_comp f hB.1)

/-- The induced homomorphism extends the given morphism of sheaves of modules: in degree one it
carries the generator of `A` to the image under `f` of the generator of `B`. -/
@[ega "II 1.7.4" "partial"]
theorem map_app_one (hA : IsSymmetricAlgebra A ι) (hB : IsSymmetricAlgebra B κ) (f : M ⟶ N) :
    ι ≫ (hA.map hB f).app 1 = f ≫ κ :=
  hA.isUniversal.desc_extends B (f ≫ κ) (pairwiseCommutes_comp f hB.1)

/-- The homomorphism induced by the identity is the identity. -/
theorem map_id (hA : IsSymmetricAlgebra A ι) : hA.map hA (𝟙 M) = UnitalHom.id A :=
  hA.isUniversal.eq_id (by rw [map_app_one, Category.id_comp])

/-- The homomorphism induced by a composite is the composite of the induced homomorphisms. -/
theorem map_comp (hA : IsSymmetricAlgebra A ι) (hB : IsSymmetricAlgebra B κ)
    (hD : IsSymmetricAlgebra D lam) (f : M ⟶ N) (f' : N ⟶ P) :
    hA.map hD (f ≫ f') = (hA.map hB f).comp (hB.map hD f') := by
  refine (hA.isUniversal.desc_unique D ((f ≫ f') ≫ lam)
    (pairwiseCommutes_comp (f ≫ f') hD.1) ?_).symm
  rw [UnitalHom.comp_app, ← Category.assoc, map_app_one, Category.assoc, map_app_one,
    Category.assoc]

/-- The map `Symⁿ M ⟶ Symⁿ N` induced by a morphism of sheaves of modules: the degree-`n`
component of `IsSymmetricAlgebra.map`. -/
noncomputable def pieceMap (hA : IsSymmetricAlgebra A ι) (hB : IsSymmetricAlgebra B κ)
    (f : M ⟶ N) (n : ℤ) : A.piece n ⟶ B.piece n :=
  (hA.map hB f).app n

/-- The map on degree-`n` symmetric powers induced by the identity is the identity. -/
@[simp,
  ega "II 1.7.4" "identity law for S"]
theorem pieceMap_id (hA : IsSymmetricAlgebra A ι) (n : ℤ) :
    hA.pieceMap hA (𝟙 M) n = 𝟙 (A.piece n) :=
  congrArg (fun g : UnitalHom A A => g.app n) hA.map_id

/-- The map on degree-`n` symmetric powers induced by a composite is the composite of the induced
maps. -/
@[ega "II 1.7.4" "composition law for S"]
theorem pieceMap_comp (hA : IsSymmetricAlgebra A ι) (hB : IsSymmetricAlgebra B κ)
    (hD : IsSymmetricAlgebra D lam) (f : M ⟶ N) (f' : N ⟶ P) (n : ℤ) :
    hA.pieceMap hD (f ≫ f') n = hA.pieceMap hB f n ≫ hB.pieceMap hD f' n :=
  congrArg (fun g : UnitalHom A D => g.app n) (hA.map_comp hB hD f f')

/-- A symmetric algebra of `N` is a symmetric algebra of `M` for the generator precomposed with
an isomorphism `c : M ⟶ N`. -/
theorem comp_isIso (hB : IsSymmetricAlgebra B κ) (c : M ⟶ N) (hc : IsIso c) :
    IsSymmetricAlgebra B (c ≫ κ) := by
  have := hc
  refine ⟨pairwiseCommutes_comp c hB.1, fun D lam hlam => ?_⟩
  obtain ⟨g, hg, hu⟩ := hB.2 D (inv c ≫ lam) (pairwiseCommutes_comp (inv c) hlam)
  refine ⟨g, ?_, fun h hh => hu h ?_⟩
  · show (c ≫ κ) ≫ g.app 1 = lam
    rw [Category.assoc, hg, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  · replace hh : (c ≫ κ) ≫ h.app 1 = lam := hh
    show κ ≫ h.app 1 = inv c ≫ lam
    rw [← hh, ← Category.assoc, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- The symmetric algebras of two isomorphic sheaves of modules are isomorphic in every degree,
by the comparison homomorphism determined by the generators and the isomorphism. -/
noncomputable def pieceIsoOfIso (hA : IsSymmetricAlgebra A ι) (hB : IsSymmetricAlgebra B κ)
    (c : M ⟶ N) (hc : IsIso c) (n : ℤ) : A.piece n ≅ B.piece n :=
  hA.isUniversal.pieceIso (hB.comp_isIso c hc).isUniversal n

/-- The map on degree-`n` symmetric powers induced by an isomorphism of sheaves of modules is an
isomorphism. -/
theorem isIso_pieceMap (hA : IsSymmetricAlgebra A ι) (hB : IsSymmetricAlgebra B κ) (f : M ⟶ N)
    (hf : IsIso f) (n : ℤ) : IsIso (hA.pieceMap hB f n) :=
  (hA.pieceIsoOfIso hB f hf n).isIso_hom

/-- A morphism of sheaves of modules with a retraction induces a split monomorphism on every
symmetric power. -/
theorem isSplitMono_pieceMap (hA : IsSymmetricAlgebra A ι) (hB : IsSymmetricAlgebra B κ)
    (f : M ⟶ N) (r : N ⟶ M) (hr : f ≫ r = 𝟙 M) (n : ℤ) :
    IsSplitMono (hA.pieceMap hB f n) :=
  IsSplitMono.mk'
    { retraction := hB.pieceMap hA r n
      id := by rw [← hA.pieceMap_comp hB hA f r n, hr, hA.pieceMap_id n] }

/-- A morphism of sheaves of modules with a retraction induces a monomorphism on every symmetric
power. -/
theorem mono_pieceMap_of_retraction (hA : IsSymmetricAlgebra A ι)
    (hB : IsSymmetricAlgebra B κ) (f : M ⟶ N) (r : N ⟶ M) (hr : f ≫ r = 𝟙 M) (n : ℤ) :
    Mono (hA.pieceMap hB f n) :=
  have := hA.isSplitMono_pieceMap hB f r hr n
  inferInstance

end IsSymmetricAlgebra

end Site

end SheafOfModules.GradedAlgebra

/-! ### The induced map for a package of tensor, exterior and symmetric algebras -/

namespace SheafOfModules.TensorExteriorSymmetricAlgebras

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {F F' F'' : SheafOfModules.{w} (Sheaf.toRingCat J Osharp)}

/-- The map on degree-`n` symmetric powers induced by a morphism of sheaves of modules, for
the symmetric algebras carried by two `TensorExteriorSymmetricAlgebras` packages. -/
noncomputable def symmetricPowerMap (A : TensorExteriorSymmetricAlgebras J F)
    (A' : TensorExteriorSymmetricAlgebras J F') (f : F ⟶ F') (n : ℤ) :
    A.symmetric.piece n ⟶ A'.symmetric.piece n :=
  A.symmetric_isSymmetricAlgebra.pieceMap A'.symmetric_isSymmetricAlgebra f n

/-- The map on degree-`n` symmetric powers induced by the identity is the identity. -/
@[simp] theorem symmetricPowerMap_id (A : TensorExteriorSymmetricAlgebras J F) (n : ℤ) :
    A.symmetricPowerMap A (𝟙 F) n = 𝟙 (A.symmetric.piece n) :=
  A.symmetric_isSymmetricAlgebra.pieceMap_id n

/-- The map on degree-`n` symmetric powers induced by a composite is the composite of the induced
maps. -/
theorem symmetricPowerMap_comp (A : TensorExteriorSymmetricAlgebras J F)
    (A' : TensorExteriorSymmetricAlgebras J F') (A'' : TensorExteriorSymmetricAlgebras J F'')
    (f : F ⟶ F') (f' : F' ⟶ F'') (n : ℤ) :
    A.symmetricPowerMap A'' (f ≫ f') n =
      A.symmetricPowerMap A' f n ≫ A'.symmetricPowerMap A'' f' n :=
  A.symmetric_isSymmetricAlgebra.pieceMap_comp A'.symmetric_isSymmetricAlgebra
    A''.symmetric_isSymmetricAlgebra f f' n

/-- The map `Sym²E ⟶ Sym²F` induced by a morphism `E ⟶ F` of sheaves of modules: the degree-two
case of `symmetricPowerMap`. -/
noncomputable abbrev symmetricSquareMap (A : TensorExteriorSymmetricAlgebras J F)
    (A' : TensorExteriorSymmetricAlgebras J F') (f : F ⟶ F') :
    A.symmetricPower 2 ⟶ A'.symmetricPower 2 :=
  A.symmetricPowerMap A' f 2

/-- `Sym²` of a morphism with a retraction is a monomorphism. -/
theorem mono_symmetricSquareMap_of_retraction (A : TensorExteriorSymmetricAlgebras J F)
    (A' : TensorExteriorSymmetricAlgebras J F') (f : F ⟶ F') (r : F' ⟶ F) (hr : f ≫ r = 𝟙 F) :
    Mono (A.symmetricSquareMap A' f) :=
  A.symmetric_isSymmetricAlgebra.mono_pieceMap_of_retraction
    A'.symmetric_isSymmetricAlgebra f r hr 2

end SheafOfModules.TensorExteriorSymmetricAlgebras

end
