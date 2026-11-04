module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPreservesColimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.RingTheory.Flat.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Flatness of the sheafification of a presheaf of modules

Let `O` be a presheaf of commutative rings on a site, `O♯` an associated sheaf of rings
presented by a locally bijective morphism `a : O ⟶ O♯`, and `F` a presheaf of `O`-modules. Two
flatness criteria for the associated sheaf `F♯` are proved: it is flat when `F` is a flat
presheaf of modules, and already when every object of the site has a covering whose members `U`
have `F(U)` flat over `O(U)`.

## Main results

* `Stacks.SheafOfModules.FlatSheafification.isFlat_sheafification`: the sheafification of a
  flat presheaf of modules is a flat sheaf of modules.
* `Stacks.SheafOfModules.FlatSheafification.isFlat_sheafification_of_locally_objectwise_flat`:
  the sheafification of a locally objectwise flat presheaf of modules is a flat sheaf of
  modules.

## References

* [Stacks Project, Tag 03ET](https://stacks.math.columbia.edu/tag/03ET)
* [Stacks Project, Tag 0GN1](https://stacks.math.columbia.edu/tag/0GN1)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w z

namespace Stacks.SheafOfModules.FlatSheafification

open AlgebraicGeometry.SheafOfModules (ringPresheaf)
open AlgebraicGeometry.SheafOfModules.PresheafOfModules (tensorObj tensorMap tensorRight)

attribute [local implicit_reducible] tensorObj tensorMap CategoryTheory.sheafCompose

private instance locallyInjective_identity_ringCat
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (P : Cᵒᵖ ⥤ RingCat.{w}) :
    Presheaf.IsLocallyInjective J (𝟙 P) where
  equalizerSieve_mem {U} x y h := by
    have hxy : x = y := by
      change x = y at h
      exact h
    apply J.superset_covering (S := ⊤)
    · intro V f hf
      rw [Presheaf.equalizerSieve_apply]
      exact congrArg (P.map f.op) hxy
    · exact J.top_mem _

private instance locallySurjective_identity_ringCat
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (P : Cᵒᵖ ⥤ RingCat.{w}) :
    Presheaf.IsLocallySurjective J (𝟙 P) where
  imageSieve_mem {U} y := by
    apply J.superset_covering (S := ⊤)
    · intro V f hf
      rw [Presheaf.imageSieve_apply]
      exact ⟨P.map f.op y, rfl⟩
    · exact J.top_mem _

/-- Tensoring on the right with `F` agrees with tensoring on the left with `F`: the symmetry
of the objectwise tensor product, sheafified. -/
private noncomputable def sheafTensorFlipIso
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [HasWeakSheafify J AddCommGrpCat.{z}]
    (O : Sheaf J CommRingCat.{w})
    (F : SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} (J := J) O).flip.obj F ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} (J := J) O).obj F :=
  let sheafificationFunctor :
      PresheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj ⥤
        SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O) :=
    PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
  (Functor.isoWhiskerLeft (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (Functor.isoWhiskerRight (TensorColimits.tensorCommIso J O F.val)
      sheafificationFunctor)).symm

/-- If `F` is objectwise flat on a covering of every object, then tensoring an objectwise
injective map with `F` gives a locally injective map. -/
private lemma locallyInjective_tensorMap_of_locallyFlat
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    (F : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}))
    (hF : ∀ U : C,
      ∃ (I : Type (max u v)) (X : I → C) (f : ∀ i, X i ⟶ U),
        Sieve.ofArrows X f ∈ J U ∧
          ∀ i, Module.Flat (O.obj (Opposite.op (X i))) (F.obj (Opposite.op (X i))))
    {G H : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w})}
    (φ : G ⟶ H)
    (hφ : ∀ U : Cᵒᵖ, Function.Injective (φ.app U).hom) :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf _).map
        ((tensorRight F).map φ)) := by
  constructor
  intro U x y hxy
  obtain ⟨I, X, f, hcov, hflat⟩ := hF U.unop
  apply J.superset_covering
    ((Sieve.generate_le_iff (Presieve.ofArrows X f)
      (Presheaf.equalizerSieve x y)).2 ((Presieve.ofArrows_le_iff).2 ?_)) hcov
  intro i
  rw [Presheaf.equalizerSieve_apply]
  let ψ := (tensorRight F).map φ
  have hinj : Function.Injective (ψ.app (Opposite.op (X i))).hom := by
    have hφi := hφ (Opposite.op (X i))
    let : Module (O.obj (Opposite.op (X i))) (F.obj (Opposite.op (X i))) :=
      (F.obj (Opposite.op (X i))).isModule
    let : Module.Flat ((O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj
        (Opposite.op (X i))) (F.obj (Opposite.op (X i))) := by
      show Module.Flat (O.obj (Opposite.op (X i))) (F.obj (Opposite.op (X i)))
      exact hflat i
    show Function.Injective
      (LinearMap.rTensor (F.obj (Opposite.op (X i)))
        (φ.app (Opposite.op (X i))).hom)
    exact Module.Flat.rTensor_preserves_injective_linearMap
      (M := F.obj (Opposite.op (X i))) (φ.app (Opposite.op (X i))).hom hφi
  change (ψ.app U).hom x = (ψ.app U).hom y at hxy
  apply hinj
  have hrel := congrArg (((tensorRight F).obj H).map (f i).op).hom hxy
  rwa [← PresheafOfModules.naturality_apply ψ (f i).op x,
    ← PresheafOfModules.naturality_apply ψ (f i).op y] at hrel

/-- Tensoring on the right with `F` preserves zero morphisms. -/
public lemma sheafTensorRight_preservesZeroMorphisms
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [HasWeakSheafify J AddCommGrpCat.{z}]
    (O : Sheaf J CommRingCat.{w})
    (F : SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} (J := J) O).flip.obj
      F).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_iso (sheafTensorFlipIso J O F).symm

/-- Tensoring on the right with `F` preserves finite colimits. -/
public lemma sheafTensorRight_preservesFiniteColimits
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [HasWeakSheafify J AddCommGrpCat.{z}]
    (O : Sheaf J CommRingCat.{w})
    (F : SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    PreservesFiniteColimits
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} (J := J) O).flip.obj F) := by
  have : PreservesFiniteColimits
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} (J := J) O).obj F) :=
    let : PreservesColimitsOfSize.{max u z, z}
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} (J := J) O).obj F) :=
      TensorColimits.tensorLeft_preservesColimits.{u, v, w, z, max u z} J O F
    PreservesColimitsOfSize.preservesFiniteColimits _
  exact preservesFiniteColimits_of_natIso (sheafTensorFlipIso J O F).symm

/-- Tensoring on the right with `F` preserves all colimits indexed in the module universe. -/
@[stacks 05NB "for the right-handed tensor endofunctor (sheafTensor O).flip.obj F"]
public lemma sheafTensorRight_preservesColimits
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [HasWeakSheafify J AddCommGrpCat.{z}]
    (O : Sheaf J CommRingCat.{w})
    (F : SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    PreservesColimitsOfSize.{max u z, z}
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} (J := J) O).flip.obj F) := by
  let : PreservesColimitsOfSize.{max u z, z}
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} (J := J) O).obj F) :=
    TensorColimits.tensorLeft_preservesColimits.{u, v, w, z, max u z} J O F
  exact preservesColimits_of_natIso (sheafTensorFlipIso J O F).symm

/-- The right-tensor map `((sheafTensor O).flip.obj F).map φ`, written with the fixed argument
given as a morphism `ψ` equal to `𝟙 F`. -/
private lemma sheafTensor_map_eq_of_eq_id
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [HasWeakSheafify J AddCommGrpCat.{z}]
    (Osharp : Sheaf J CommRingCat.{w})
    (F : SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp))
    {G H : SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
    (ψ : F ⟶ F) (hψ : ψ = 𝟙 F) (φ : G ⟶ H) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} Osharp).map φ).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} Osharp).obj _).map ψ) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} Osharp).flip.obj F).map φ := by
  subst hψ
  exact (congrArg (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z}
    Osharp).map φ).app F ≫ ·)
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} Osharp).obj H).map_id F)).trans
    (Category.comp_id _)

/-- A morphism of presheaves of modules whose underlying morphism of presheaves of abelian
groups is locally injective becomes a monomorphism after sheafification. -/
public lemma moduleSheafification_map_mono_of_locallyInjective
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {R₀ : Cᵒᵖ ⥤ RingCat.{w}} {R : Sheaf J RingCat.{w}}
    (α : R₀ ⟶ R.obj) [Presheaf.IsLocallyInjective J α]
    [Presheaf.IsLocallySurjective J α]
    [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [HasWeakSheafify J AddCommGrpCat.{z}]
    {M N : PresheafOfModules.{z} R₀} (f : M ⟶ N)
    (hf : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf R₀).map f)) :
    Mono ((PresheafOfModules.sheafification α).map f) := by
  have hli : Sheaf.IsLocallyInjective
      ((presheafToSheaf J AddCommGrpCat.{z}).map
        ((PresheafOfModules.toPresheaf R₀).map f)) :=
    (Presheaf.isLocallyInjective_presheafToSheaf_map_iff J _).2 hf
  have hm : Mono ((presheafToSheaf J AddCommGrpCat.{z}).map
      ((PresheafOfModules.toPresheaf R₀).map f)) :=
    Sheaf.mono_of_isLocallyInjective _
  apply Functor.mono_of_mono_map (SheafOfModules.toSheaf R)
  let η := PresheafOfModules.sheafificationCompToSheaf α
  have hcomp : Mono
    ((SheafOfModules.toSheaf R).map ((PresheafOfModules.sheafification α).map f) ≫
        η.hom.app N) := by
    rw [← Functor.comp_map, η.hom.naturality f]
    show Mono (η.hom.app M ≫
      (presheafToSheaf J AddCommGrpCat.{z}).map
        ((PresheafOfModules.toPresheaf R₀).map f))
    exact mono_comp _ _
  exact (mono_comp_iff_of_mono _ _).1 hcomp

/-- Transport of a monomorphism `(Q ⋙ S).map (φ₀, 𝟙 F₀)` along `α : S.prod S ⋙ T ≅ Q ⋙ S` and
isomorphisms `S.obj G₀ ≅ G`, `S.obj H₀ ≅ H` compatible with `φ₀` and `φ`. -/
private lemma productMap_mono_of_sheafificationIso
    {A : Type u} {B : Type v}
    [Category A] [Category B]
    (S : A ⥤ B) (Q : A × A ⥤ A) (T : B × B ⥤ B)
    (α : (S.prod S) ⋙ T ≅ Q ⋙ S)
    {G₀ H₀ F₀ : A} {G H : B}
    (φ₀ : G₀ ⟶ H₀) (φ : G ⟶ H)
    (eG : S.obj G₀ ≅ G) (eH : S.obj H₀ ≅ H)
    (hmap : S.map φ₀ ≫ eH.hom = eG.hom ≫ φ)
    (hQ : Mono ((Q ⋙ S).map
      (show (G₀, F₀) ⟶ (H₀, F₀) from (φ₀, 𝟙 F₀)))) :
    Mono (T.map (show (G, S.obj F₀) ⟶ (H, S.obj F₀) from
      (φ, 𝟙 (S.obj F₀)))) := by
  let p : (G₀, F₀) ⟶ (H₀, F₀) := (φ₀, 𝟙 F₀)
  have : Mono ((Q ⋙ S).map p) := hQ
  have : Mono (((S.prod S) ⋙ T).map p) := by
    have : Mono (((S.prod S) ⋙ T).map p ≫ α.hom.app (H₀, F₀)) := by
      rw [α.hom.naturality p]
      infer_instance
    exact mono_of_mono _ (α.hom.app (H₀, F₀))
  have htransport : (S.prod S).map p ≫ (eH.prod (Iso.refl _)).hom =
      (eG.prod (Iso.refl _)).hom ≫ (φ, 𝟙 (S.obj F₀)) :=
    Prod.ext hmap (by simp [p])
  have h := congrArg T.map htransport
  rw [T.map_comp, T.map_comp] at h
  have : Mono (T.map (eG.prod (Iso.refl _)).hom ≫
      T.map (show (G, S.obj F₀) ⟶ (H, S.obj F₀) from (φ, 𝟙 (S.obj F₀)))) := by
    rw [← h]
    exact mono_comp (((S.prod S) ⋙ T).map p) _
  exact (mono_comp_iff_of_isIso _ _).1 this

/-- Tensoring on the right with the sheafification of `F₀` preserves monomorphisms, provided
tensoring on the right with `F₀` sends objectwise injective maps to locally injective ones. -/
private lemma sheafTensor_flip_map_mono
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [HasWeakSheafify J AddCommGrpCat.{z}]
    {O : Cᵒᵖ ⥤ CommRingCat.{w}} {Osharp : Sheaf J CommRingCat.{w}}
    (a : O ⋙ forget₂ CommRingCat.{w} RingCat.{w} ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)
    [Presheaf.IsLocallyInjective J a] [Presheaf.IsLocallySurjective J a]
    {F₀ : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w})}
    (hloc : ∀ {G₀ H₀ : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w})}
      (ψ : G₀ ⟶ H₀), (∀ U : Cᵒᵖ, Function.Injective (ψ.app U).hom) →
        Presheaf.IsLocallyInjective J
          ((PresheafOfModules.toPresheaf (O ⋙ forget₂ CommRingCat.{w} RingCat.{w})).map
            ((tensorRight F₀).map ψ)))
    (G H : SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp))
    (φ : G ⟶ H) [Mono φ] :
    Mono (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} Osharp).flip.obj
      ((PresheafOfModules.sheafification
        (R := Stacks.SheafOfModules.Tensor.ringSheaf Osharp) a).obj F₀)).map φ) := by
  let ac : O ⟶ Osharp.obj := {
    app := fun U => CommRingCat.ofHom (a.app U).hom
    naturality := by
      intro U V f
      apply (forget₂ CommRingCat.{w} RingCat.{w}).map_injective
      show (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).map f ≫ a.app V =
        a.app U ≫ (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.map f
      exact a.naturality f
  }
  let ρ := CategoryTheory.Sheaf.toRingCatMap J ac
  have hρ : ρ = a := by
    dsimp [ρ, CategoryTheory.Sheaf.toRingCatMap, Stacks.SheafOfModules.Tensor.ringSheaf]
    ext U
    rfl
  have : Presheaf.IsLocallyInjective J ρ := (inferInstance : Presheaf.IsLocallyInjective J a)
  have : Presheaf.IsLocallySurjective J ρ :=
    (inferInstance : Presheaf.IsLocallySurjective J a)
  let S := _root_.PresheafOfModules.moduleSheafification.{v, u, w, z} J ac
  let G₀ := (PresheafOfModules.restrictScalars ρ).obj G.val
  let H₀ := (PresheafOfModules.restrictScalars ρ).obj H.val
  let φ₀ : G₀ ⟶ H₀ := (PresheafOfModules.restrictScalars ρ).map φ.val
  let T := (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} Osharp))
  let τ := _root_.PresheafOfModules.tensorHom.{v, u, w, z, z} φ₀ (𝟙 F₀)
  have hτ : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (O ⋙ forget₂ CommRingCat.{w} RingCat.{w})).map τ) := by
    show Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (O ⋙ forget₂ CommRingCat.{w} RingCat.{w})).map
        ((tensorRight F₀).map φ₀))
    let : PreservesFiniteLimits (SheafOfModules.forget.{z}
        (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)) :=
      SheafOfModules.Finite.forgetPreservesFiniteLimits _
    have hmono : Mono ((SheafOfModules.forget.{z}
        (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)).map φ) := Functor.map_mono _ φ
    exact hloc φ₀ (by
      intro U
      show Function.Injective (((SheafOfModules.forget
        (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)).map φ).app U).hom
      exact PresheafOfModules.injective_of_mono _ U)
  have hτmono : Mono ((PresheafOfModules.sheafification.{z, v, w, u} ρ).map τ) :=
    moduleSheafification_map_mono_of_locallyInjective J ρ τ hτ
  let α := _root_.PresheafOfModules.sheafificationTensorIso.{v, u, w, z, z} J ac
  have hτmonoS : Mono (S.map τ) := by
    simpa only [S] using hτmono
  let adj := PresheafOfModules.sheafificationAdjunction.{z, v, w, u}
    (R₀ := O ⋙ forget₂ CommRingCat.{w} RingCat.{w})
    (R := CategoryTheory.Sheaf.toRingCat J Osharp) (α := ρ)
  have : IsIso adj.counit := by infer_instance
  have hG : IsIso (adj.counit.app G) := NatIso.isIso_app_of_isIso adj.counit G
  have hH : IsIso (adj.counit.app H) := NatIso.isIso_app_of_isIso adj.counit H
  let eG : S.obj G₀ ≅ G := @asIso _ _ _ _ _ hG
  let eH : S.obj H₀ ≅ H := @asIso _ _ _ _ _ hH
  have hmap : S.map φ₀ ≫ eH.hom = eG.hom ≫ φ := adj.counit.naturality φ
  let p₀ : (G₀, F₀) ⟶ (H₀, F₀) := (φ₀, 𝟙 F₀)
  have hQ : Mono
      (((Functor.uncurry.obj (PresheafOfModules.tensorBifunctor.{v, u, w, z, z} O)) ⋙ S).map
        p₀) :=
    (congrArg (fun morphism ↦ Mono (S.map morphism))
      (_root_.PresheafOfModules.tensorBifunctor_uncurry_map (O := O) φ₀ (𝟙 F₀))).mpr hτmonoS
  show Mono (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} Osharp).flip.obj
    (S.obj F₀)).map φ)
  have tensorMono := productMap_mono_of_sheafificationIso S
    ((Functor.uncurry.obj (PresheafOfModules.tensorBifunctor.{v, u, w, z, z} O))) T α
    φ₀ φ eG eH hmap (by simpa only [p₀] using hQ)
  exact (congrArg Mono
    (sheafTensor_map_eq_of_eq_id J Osharp (S.obj F₀) (𝟙 _) rfl φ)).mp tensorMono

/-- A sheaf of modules is flat as soon as tensoring with it preserves monomorphisms. -/
private lemma isFlat_of_sheafTensor_flip_map_mono
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
    [HasWeakSheafify J AddCommGrpCat.{z}]
    (Osharp : Sheaf J CommRingCat.{w})
    (F : SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp))
    (hmono : ∀ (G H : SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp))
      (φ : G ⟶ H) [Mono φ],
      Mono (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} (J := J) Osharp).flip.obj
        F).map φ)) :
    AlgebraicGeometry.SheafOfModules.IsFlat F := by
  let T := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, z, z} (J := J) Osharp).flip.obj F
  have : T.PreservesMonomorphisms := ⟨fun φ hφ => hmono _ _ φ⟩
  have : PreservesFiniteColimits T := sheafTensorRight_preservesFiniteColimits J Osharp F
  have : T.PreservesZeroMorphisms := sheafTensorRight_preservesZeroMorphisms J Osharp F
  have : T.PreservesHomology := Functor.preservesHomology_of_preservesMonos_and_cokernels T
  have : ∀ {X Y : SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)} (f : X ⟶ Y),
      PreservesLimit (parallelPair f 0) T :=
    fun f => Functor.PreservesHomology.preservesKernels (F := T) f
  have hlim : PreservesFiniteLimits T := T.preservesFiniteLimits_of_preservesKernels
  show exactFunctor _ _ T
  exact (exactFunctor_iff T).2 ⟨hlim, inferInstance⟩

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
  [HasWeakSheafify J AddCommGrpCat.{z}]

/-- If a presheaf of modules is objectwise flat after passing to a covering of every object,
then its associated sheaf is flat. -/
@[stacks 0GN1]
public lemma isFlat_sheafification_of_locally_objectwise_flat
    {O : Cᵒᵖ ⥤ CommRingCat.{w}} {Osharp : Sheaf J CommRingCat.{w}}
    (a : O ⋙ forget₂ CommRingCat.{w} RingCat.{w} ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)
    [Presheaf.IsLocallyInjective J a]
    [Presheaf.IsLocallySurjective J a]
    (F : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}))
    (hF : ∀ U : C,
      ∃ (I : Type (max u v)) (X : I → C) (f : ∀ i, X i ⟶ U),
        Sieve.ofArrows X f ∈ J U ∧
          ∀ i, Module.Flat (O.obj (Opposite.op (X i))) (F.obj (Opposite.op (X i)))) :
    AlgebraicGeometry.SheafOfModules.IsFlat
      ((PresheafOfModules.sheafification
        (R := Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
        a).obj F) := by
  have : HasSheafify J AddCommGrpCat.{z} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective (J := J)
  exact isFlat_of_sheafTensor_flip_map_mono J Osharp _ fun G H φ _ =>
    sheafTensor_flip_map_mono J a
      (fun ψ hψ => locallyInjective_tensorMap_of_locallyFlat J F hF ψ hψ) G H φ


section SheafificationFlatness

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
  [HasWeakSheafify J AddCommGrpCat.{z}]

/-- The sheaf associated to a flat presheaf of modules is flat over the associated sheaf of
rings. -/
@[stacks 03ET]
public lemma isFlat_sheafification
    {O : Cᵒᵖ ⥤ CommRingCat.{w}} {Osharp : Sheaf J CommRingCat.{w}}
    (a : O ⋙ forget₂ CommRingCat.{w} RingCat.{w} ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)
    [Presheaf.IsLocallyInjective J a]
    [Presheaf.IsLocallySurjective J a]
    (F : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}))
    (hF : AlgebraicGeometry.SheafOfModules.PresheafOfModules.IsFlat F) :
    AlgebraicGeometry.SheafOfModules.IsFlat
      ((PresheafOfModules.sheafification
        (R := Stacks.SheafOfModules.Tensor.ringSheaf Osharp) a).obj F) := by
  have : PreservesFiniteLimits (tensorRight (O := O) F) := ((exactFunctor_iff _).mp hF).1
  have : (tensorRight (O := O) F).PreservesMonomorphisms := inferInstance
  refine isFlat_of_sheafTensor_flip_map_mono J Osharp _ fun G H φ _ =>
    sheafTensor_flip_map_mono J a (F₀ := F) (fun {G₀ H₀} ψ hψ => ?_) G H φ
  have : Mono ψ := PresheafOfModules.mono_of_injective (f := ψ) (fun {U} => hψ U)
  have : Mono ((tensorRight (O := O) F).map ψ) := Functor.map_mono _ ψ
  exact Presheaf.isLocallyInjective_of_injective J _
    (fun U => PresheafOfModules.injective_of_mono ((tensorRight (O := O) F).map ψ) U)

end SheafificationFlatness

end Stacks.SheafOfModules.FlatSheafification

end
