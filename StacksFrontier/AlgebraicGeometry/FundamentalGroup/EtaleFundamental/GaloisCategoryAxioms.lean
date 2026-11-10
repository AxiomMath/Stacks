module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.Etale.Finite
public import StacksFrontier.AlgebraicGeometry.FiniteEtaleColimits.Basic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.ChangeBasePoint
public import StacksFrontier.Topology.Connected.FiniteFibres
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Galois-category axioms for finite étale covers: everything except right exactness

Let `X` be a connected scheme and `x` a geometric point of `X`. Stacks Tag 0BNB says that the
geometric fibre functor `F_x : FÉt_X ⥤ Type` makes `FÉt_X` a Galois category, i.e. satisfies the
six axioms of `CategoryTheory.IsGaloisCategory`. This file proves **five of the six**;
the sixth is proved in
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/FiniteEtaleGaloisCategory.lean`, the instance is
assembled in
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/GaloisCategories/FiberFunctorComplete.lean`, and
the two factorisations of the fibre functor that this file keeps `private` are what they consume.

The engine is the identification of `FÉt_{Spec K}` with the finite étale `K`-algebras, which for
`K` separably closed Mathlib identifies with finite sets
(`CommAlgCat.FiniteEtale.equivOfIsSepClosed`). Base changing along `x : Spec Ω ⟶ X` and
corepresenting by the identity cover turns `F_x` into a composite of base change with a `coyoneda`,
which is where finiteness of the fibres comes from; corepresenting instead in schemes over `X`
gives left exactness.

## What is proved, and the one axiom that is missing

| axiom of `IsGaloisCategory` | status |
| --- | --- |
| `hasFiniteLimits` | proved elsewhere, `Stacks.FundamentalGroup.hasFiniteLimits_finiteEtaleOver` |
| `hasFiniteColimits` | proved elsewhere,
  `Stacks.FundamentalGroup.hasFiniteColimits_finiteEtaleOver` |
| `finite_obj` | here, `AlgebraicGeometry.finite_finiteEtaleFiber` |
| `reflectsIsomorphisms` | here, `AlgebraicGeometry.reflectsIsomorphisms_finiteEtaleFiberFunctor` |
| `exists_finite_coproduct_connected` | here,
  `AlgebraicGeometry.exists_finiteCoproduct_isConnected_finiteEtaleOver` |
| `exact`, limit half | here, `AlgebraicGeometry.preservesFiniteLimits_finiteEtaleFiberFunctor` |
| `exact`, **colimit half** |
  `StacksFrontier/AlgebraicGeometry/FundamentalGroup/FiniteEtaleGaloisCategory.lean`,
  `preservesFiniteColimits_finiteEtaleFiberFunctor` |

Tag 0BNB is reduced to the single statement
`CategoryTheory.Limits.PreservesFiniteColimits (finiteEtaleFiberFunctor x)`, and the route that
proves it is the factorisation `AlgebraicGeometry.fiberIsoPointCoyoneda`, which needs
`PreservesFiniteColimits (finiteEtaleBaseChange x.hom)` for the morphism from the spectrum of the
residue field — the fourth assertion of Stacks Tag 0BN9 at a geometric point, which is
`Stacks.FundamentalGroup.preservesFiniteColimits_finiteEtaleBaseChange_geometricPoint`.

The other factorisation `AlgebraicGeometry.fiberIsoCoyoneda` does **not** reduce the statement to
part (1) of Tag 0BNA: the second factor there is `coyoneda.obj (op (Over.mk x.hom))` on `Over X`,
and a hom-functor does not preserve colimits, so preservation by the composite does not follow
from preservation by the forgetful functor. `pointCoyoneda_preservesFiniteColimits` is the
corresponding fact for the *other* factorisation, where the second factor is corepresented by a
terminal object of `FÉt_{Spec Ω}` and the category is equivalent to finite sets.

No `@[stacks 0BNB]` attribute appears here: the covering set of that tag is the single instance
asserting all six axioms, and that instance is
`AlgebraicGeometry.finiteEtaleFiberFunctor_isGaloisCategory` of
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/GaloisCategories/FiberFunctorComplete.lean`.

## Why `finite_finiteEtaleFiber` is worth having on its own

It is declared as an instance, and it is exactly the hypothesis
`∀ Y, Finite ((finiteEtaleFiberFunctor x).obj Y)` that the conditional instances
`AlgebraicGeometry.etaleFundamentalGroupCompactSpace`,
`AlgebraicGeometry.etaleFundamentalGroupT2Space` and
`AlgebraicGeometry.etaleFundamentalGroupTotallyDisconnectedSpace` of
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/EtaleFundamentalGroup.lean` take. With it in
scope those fire, so the étale fundamental group of a connected scheme is **unconditionally**
compact, Hausdorff and totally disconnected — profinite in the sense of Stacks 0BMR — with no
appeal to Tag 0BNB.

## Main results

* `AlgebraicGeometry.finite_finiteEtaleFiber` and
  `AlgebraicGeometry.forall_finite_finiteEtaleFiberFunctor_obj` — the geometric fibres are finite.
* `AlgebraicGeometry.compactSpace_etaleFundamentalGroup`,
  `AlgebraicGeometry.t2Space_etaleFundamentalGroup` and
  `AlgebraicGeometry.totallyDisconnectedSpace_etaleFundamentalGroup` — consequently `π₁(X, x)` is
  profinite, with no hypothesis.
* `AlgebraicGeometry.preservesFiniteLimits_finiteEtaleFiberFunctor`,
  `AlgebraicGeometry.reflectsIsomorphisms_finiteEtaleFiberFunctor` and
  `AlgebraicGeometry.exists_finiteCoproduct_isConnected_finiteEtaleOver` — the other three
  Galois-category axioms this file supplies.

The two factorisations of the fibre functor and the equivalence
`FÉt_{Spec K} ≌ (finite étale K-algebras)ᵒᵖ` that drives them are `private`, because their bodies
name other private helpers and the 4.34 module system will not expose such a body.
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/GaloisCategories/FiberFunctorComplete.lean`
reaches them with `import all` on this module rather than re-deriving them.

## Implementation notes

Neither `set_option backward.isDefEq.respectTransparency false` nor
`set_option backward.defeqAttrib.useBackward true` is needed over the Spec-point block. The
morphism property is written as the abbreviation `AlgebraicGeometry.finiteEtale` rather than as
`(@IsFinite : MorphismProperty Scheme) ⊓ @Etale`; with this spelling the terms stay type-correct
at `implicit` transparency. The one residual crossing, in
`finiteEtaleSpecPoint_full`, is a `rw [Spec.map_preimage]` under a composition, and is written in
term mode with `congrArg` instead — the device the neighbouring `MorphismMap.lean` already uses.

Likewise the category of covers of a point is `AlgebraicGeometry.FiniteEtaleOver`
applied to `Spec K`, not a new abbreviation, and the colimit reflection in
`exists_finiteCoproduct_isConnected_finiteEtaleOver` is
`Stacks.FundamentalGroup.isColimitOfIsColimitCoconeLeft` rather than an appeal to the forgetful
functor preserving colimits — which is what keeps that proof clear of the missing axiom.

## References

* [Stacks Project, Tag 0BNB](https://stacks.math.columbia.edu/tag/0BNB)
* [Stacks Project, Tag 0BN9](https://stacks.math.columbia.edu/tag/0BN9)
* [Stacks Project, Tag 0BNA](https://stacks.math.columbia.edu/tag/0BNA)
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace AlgebraicGeometry

/-- Taking the relative spectrum sends a finite étale `K`-algebra to a finite étale cover of
`Spec K`, contravariantly. -/
private noncomputable def finiteEtaleSpecPoint (K : Type u) [CommRing K] :
    (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ ⥤ FiniteEtaleOver (Spec (.of K)) where
  obj B := MorphismProperty.Over.mk ⊤
    (Spec.map (CommRingCat.ofHom (algebraMap K B.unop.obj)))
      ⟨(IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance),
        (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
          (RingHom.etale_algebraMap.mpr inferInstance)⟩
  map {B C} f := MorphismProperty.Over.homMk
      (Spec.map (CommRingCat.ofHom f.unop.hom.hom)) <| by
    change Spec.map (CommRingCat.ofHom f.unop.hom.hom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K C.unop.obj)) =
      Spec.map (CommRingCat.ofHom (algebraMap K B.unop.obj))
    rw [← Spec.map_comp]
    exact Spec.map_inj.mpr (by ext r; exact f.unop.hom.hom.commutes r)
  map_id B := by
    apply MorphismProperty.Over.Hom.ext
    change Spec.map (CommRingCat.ofHom _) = 𝟙 _
    simp
  map_comp f g := by
    apply MorphismProperty.Over.Hom.ext
    change Spec.map (CommRingCat.ofHom _) = Spec.map (CommRingCat.ofHom _) ≫
      Spec.map (CommRingCat.ofHom _)
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl

private lemma finiteEtaleSpecPoint_faithful (K : Type u) [CommRing K] :
    (finiteEtaleSpecPoint K).Faithful where
  map_injective {X Y} {f g} h := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    have hh := congrArg (fun k => k.left) h
    change Spec.map (CommRingCat.ofHom f.unop.hom.hom.toRingHom) =
      Spec.map (CommRingCat.ofHom g.unop.hom.hom.toRingHom) at hh
    apply AlgHom.toRingHom_injective
    exact congrArg CommRingCat.Hom.hom (Spec.map_inj.mp hh)

private lemma finiteEtaleSpecPoint_full (K : Type u) [CommRing K] :
    (finiteEtaleSpecPoint K).Full where
  map_surjective {X Y} f := by
    dsimp [finiteEtaleSpecPoint] at f
    let g : Y.unop.obj →+* X.unop.obj := (Spec.preimage f.left).hom
    have hg : g.comp (algebraMap K Y.unop.obj) = algebraMap K X.unop.obj := by
      have hw : CommRingCat.ofHom (algebraMap K Y.unop.obj) ≫ CommRingCat.ofHom g =
          CommRingCat.ofHom (algebraMap K X.unop.obj) := by
        apply Spec.map_inj.mp
        rw [Spec.map_comp]
        exact (congrArg (· ≫ Spec.map (CommRingCat.ofHom (algebraMap K Y.unop.obj)))
          (Spec.map_preimage f.left)).trans (MorphismProperty.Over.w f)
      exact congrArg CommRingCat.Hom.hom hw
    let ga : Y.unop.obj →ₐ[K] X.unop.obj := ⟨g, fun r => RingHom.congr_fun hg r⟩
    exact ⟨(ObjectProperty.homMk (CommAlgCat.ofHom ga)).op,
      MorphismProperty.Over.Hom.ext (Spec.map_preimage f.left)⟩

private lemma finiteEtaleSpecPoint_essSurj (K : Type u) [CommRing K] :
    (finiteEtaleSpecPoint K).EssSurj := by
  refine ⟨fun X => ?_⟩
  let : IsFinite X.hom := X.prop.1
  let : Etale X.hom := X.prop.2
  let : IsAffineHom X.hom := inferInstance
  let : IsAffine ((Functor.fromPUnit (Spec (CommRingCat.of K))).obj X.right) := by
    change IsAffine (Spec (CommRingCat.of K))
    infer_instance
  let : IsAffine X.left := isAffine_of_isAffineHom X.hom
  let φ : CommRingCat.of K ⟶ CommRingCat.of Γ(X.left, ⊤) :=
    Spec.preimage (X.left.isoSpec.inv ≫ X.hom)
  let : Algebra K Γ(X.left, ⊤) := φ.hom.toAlgebra
  have hfin : Module.Finite K Γ(X.left, ⊤) := by
    rw [← RingHom.finite_algebraMap]
    exact (IsFinite.SpecMap_iff φ).mp (by rw [Spec.map_preimage]; infer_instance)
  have heta : Algebra.Etale K Γ(X.left, ⊤) := by
    rw [← RingHom.etale_algebraMap]
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp
      (by rw [Spec.map_preimage]; infer_instance)
  let := hfin
  let := heta
  let B := CommAlgCat.FiniteEtale.of K Γ(X.left, ⊤)
  refine ⟨Opposite.op B, ⟨MorphismProperty.Over.isoMk X.left.isoSpec.symm ?_⟩⟩
  change X.left.isoSpec.inv ≫ X.hom =
    Spec.map (CommRingCat.ofHom (algebraMap K Γ(X.left, ⊤)))
  change X.left.isoSpec.inv ≫ X.hom = Spec.map φ
  rw [Spec.map_preimage]

private lemma finiteEtaleSpecPoint_isEquivalence (K : Type u) [CommRing K] :
    (finiteEtaleSpecPoint K).IsEquivalence := by
  have := finiteEtaleSpecPoint_faithful K
  have := finiteEtaleSpecPoint_full K
  have := finiteEtaleSpecPoint_essSurj K
  exact Functor.IsEquivalence.mk


private noncomputable def fiberIsoCoyoneda {X : Scheme.{u}} (x : GeometricPoint X) :
    finiteEtaleFiberFunctor x ≅
      finiteEtaleOverForgetOver X ⋙ coyoneda.obj (Opposite.op (Over.mk x.hom)) :=
  NatIso.ofComponents (fun Y =>
    (Equiv.ofBijective
      (fun (p : finiteEtaleFiber x Y) => Over.homMk p.1 p.2)
      ⟨fun _ _ hp => Subtype.ext (by exact congrArg CommaMorphism.left hp),
        fun f => ⟨⟨f.left, Over.w f⟩, by ext; rfl⟩⟩).toIso) (by
    intro Y Z f
    ext p
    rfl)

private lemma fiber_preservesFiniteLimits {X : Scheme.{u}} (x : GeometricPoint X) :
    PreservesFiniteLimits (finiteEtaleFiberFunctor x) :=
  preservesFiniteLimits_of_natIso (fiberIsoCoyoneda x).symm

private lemma finite_hom_over_point (K : Type u) [Field K] [IsSepClosed K]
    (Y Z : FiniteEtaleOver (Spec (.of K))) : Finite (Y ⟶ Z) := by
  let hfin (A B : (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ) : Finite (A ⟶ B) := by
    let : (CommAlgCat.FiniteEtale.finiteSpec.{u} K).Faithful :=
      (CommAlgCat.FiniteEtale.equivOfIsSepClosed K).isEquivalence_functor.faithful
    exact Finite.of_injective
      (fun f => (CommAlgCat.FiniteEtale.finiteSpec K).map f)
      (fun _ _ h => (CommAlgCat.FiniteEtale.finiteSpec K).map_injective h)
  let : (finiteEtaleSpecPoint K).IsEquivalence := finiteEtaleSpecPoint_isEquivalence K
  let E := (finiteEtaleSpecPoint K).asEquivalence
  exact Finite.of_injective (fun f => E.inverse.map f)
    (fun _ _ h => E.inverse.map_injective h)

private noncomputable def pointEquivFin (K : Type u) [Field K] [IsSepClosed K] :
    FiniteEtaleOver (Spec (.of K)) ≌ FintypeCat.{u} :=
  letI : (finiteEtaleSpecPoint K).IsEquivalence := finiteEtaleSpecPoint_isEquivalence K
  (finiteEtaleSpecPoint K).asEquivalence.symm.trans
    (CommAlgCat.FiniteEtale.equivOfIsSepClosed K)

private def finiteEtalePointId (K : Type u) [Field K] : FiniteEtaleOver (Spec (.of K)) :=
  MorphismProperty.Over.mk ⊤ (𝟙 (Spec (.of K))) (by constructor <;> infer_instance)

private def finiteEtalePointId_terminal (K : Type u) [Field K] :
    IsTerminal (finiteEtalePointId K) := by
  let : (finiteEtale : MorphismProperty Scheme.{u}).ContainsIdentities :=
    ⟨fun _ => by constructor <;> infer_instance⟩
  exact MorphismProperty.Over.mkIdTerminal finiteEtale (Spec (.of K))

private def coyonedaFiniteTerminalIso (T : FintypeCat.{u}) [Unique T] :
    coyoneda.obj (Opposite.op T) ≅ FintypeCat.incl :=
  NatIso.ofComponents (fun Z =>
    (Equiv.ofBijective (fun (f : T ⟶ Z) => f default)
      ⟨fun f g h => by ext t; simpa only [Subsingleton.elim t default] using h,
        fun z => ⟨FintypeCat.homMk (fun _ => z), rfl⟩⟩).toIso) (by
    intro Z W f
    ext g
    rfl)

private noncomputable def pointCoyonedaIso (K : Type u) [Field K] [IsSepClosed K] :
    coyoneda.obj (Opposite.op (finiteEtalePointId K)) ≅
      (pointEquivFin K).functor ⋙ FintypeCat.incl := by
  let E := pointEquivFin K
  let I := finiteEtalePointId K
  let hI : IsTerminal I := finiteEtalePointId_terminal K
  let hEI : IsTerminal (E.functor.obj I) := hI.isTerminalObj E.functor
  letI : Unique (E.functor.obj I) :=
    Types.isTerminalEquivUnique _ (hEI.isTerminalObj FintypeCat.incl)
  let e : coyoneda.obj (Opposite.op I) ≅
      E.functor ⋙ coyoneda.obj (Opposite.op (E.functor.obj I)) :=
    NatIso.ofComponents (fun Z => (E.fullyFaithfulFunctor.homEquiv).toIso) (by
      intro Z W f
      ext g
      simp)
  exact e ≪≫ Functor.isoWhiskerLeft E.functor
    (coyonedaFiniteTerminalIso (E.functor.obj I))

private lemma pointCoyoneda_preservesFiniteColimits (K : Type u) [Field K] [IsSepClosed K] :
    PreservesFiniteColimits (coyoneda.obj (Opposite.op (finiteEtalePointId K))) := by
  let E := pointEquivFin K
  let : E.functor.IsEquivalence := E.isEquivalence_functor
  let : PreservesFiniteColimits E.functor := by infer_instance
  let : PreservesFiniteColimits (E.functor ⋙ FintypeCat.incl) := by infer_instance
  exact preservesFiniteColimits_of_natIso (pointCoyonedaIso K).symm


private def fiberPointHomEquiv {X : Scheme.{u}} (x : GeometricPoint X) (Y : FiniteEtaleOver X) :
    finiteEtaleFiber x Y ≃
      (finiteEtalePointId x.residueField ⟶ (finiteEtaleBaseChange x.hom).obj Y) where
  toFun p := MorphismProperty.Over.homMk
    (pullback.lift p.1 (𝟙 _)
      (by change p.1 ≫ Y.hom = (𝟙 x.source) ≫ x.hom
          simpa using p.2))
    (pullback.lift_snd _ _ _)
  invFun f := ⟨f.left ≫ pullback.fst Y.hom x.hom, by
    have hf := MorphismProperty.Over.w f
    change f.left ≫ pullback.snd Y.hom x.hom = 𝟙 x.source at hf
    have h := congrArg (f.left ≫ ·) (pullback.condition (f := Y.hom) (g := x.hom))
    have h' := (Category.assoc f.left (pullback.fst Y.hom x.hom) Y.hom).trans
      (h.trans (Category.assoc f.left (pullback.snd Y.hom x.hom) x.hom).symm)
    exact h'.trans ((congrArg (· ≫ x.hom) hf).trans (Category.id_comp x.hom))⟩
  left_inv p := Subtype.ext (pullback.lift_fst _ _ _)
  right_inv f := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · have hf := MorphismProperty.Over.w f
      change f.left ≫ pullback.snd Y.hom x.hom = 𝟙 x.source at hf
      change pullback.lift _ _ _ ≫ pullback.snd Y.hom x.hom =
        f.left ≫ pullback.snd Y.hom x.hom
      exact (pullback.lift_snd _ _ _).trans hf.symm

private def fiberIsoPointCoyoneda {X : Scheme.{u}} (x : GeometricPoint X) :
    finiteEtaleFiberFunctor x ≅
      finiteEtaleBaseChange x.hom ⋙
        coyoneda.obj (Opposite.op (finiteEtalePointId x.residueField)) :=
  NatIso.ofComponents (fun Y => (fiberPointHomEquiv x Y).toIso) (by
    intro Y Z f
    ext p
    change (fiberPointHomEquiv x Z) ((finiteEtaleFiberFunctor x).map f p) =
      (fiberPointHomEquiv x Y p) ≫ (finiteEtaleBaseChange x.hom).map f
    let a := (fiberPointHomEquiv x Y p).left
    let b := ((finiteEtaleBaseChange x.hom).map f).left
    let c := (fiberPointHomEquiv x Z ((finiteEtaleFiberFunctor x).map f p)).left
    have ha₁ : a ≫ pullback.fst Y.hom x.hom = p.1 := by
      change pullback.lift _ _ _ ≫ pullback.fst Y.hom x.hom = p.1
      exact pullback.lift_fst _ _ _
    have ha₂ : a ≫ pullback.snd Y.hom x.hom = 𝟙 x.source :=
      MorphismProperty.Over.w (fiberPointHomEquiv x Y p)
    have hb₁ : b ≫ pullback.fst Z.hom x.hom = pullback.fst Y.hom x.hom ≫ f.left := by
      change pullback.lift _ _ _ ≫ pullback.fst Z.hom x.hom = _
      exact pullback.lift_fst _ _ _
    have hb₂ : b ≫ pullback.snd Z.hom x.hom = pullback.snd Y.hom x.hom := by
      change pullback.lift _ _ _ ≫ pullback.snd Z.hom x.hom = _
      exact pullback.lift_snd _ _ _
    have hc₁ : c ≫ pullback.fst Z.hom x.hom = p.1 ≫ f.left := by
      change pullback.lift _ _ _ ≫ pullback.fst Z.hom x.hom = _
      exact pullback.lift_fst _ _ _
    have hc₂ : c ≫ pullback.snd Z.hom x.hom = 𝟙 x.source :=
      MorphismProperty.Over.w (fiberPointHomEquiv x Z ((finiteEtaleFiberFunctor x).map f p))
    refine MorphismProperty.Over.Hom.ext (pullback.hom_ext ?_ ?_)
    · change c ≫ pullback.fst Z.hom x.hom = (a ≫ b) ≫ pullback.fst Z.hom x.hom
      exact hc₁.trans ((Category.assoc a b _).trans ((congrArg (a ≫ ·) hb₁).trans
        ((Category.assoc a _ f.left).symm.trans (congrArg (· ≫ f.left) ha₁)))).symm
    · change c ≫ pullback.snd Z.hom x.hom = (a ≫ b) ≫ pullback.snd Z.hom x.hom
      exact hc₂.trans ((Category.assoc a b _).trans ((congrArg (a ≫ ·) hb₂).trans ha₂)).symm)

private lemma fiber_finite {X : Scheme.{u}} (x : GeometricPoint X) (Y : FiniteEtaleOver X) :
    Finite ((finiteEtaleFiberFunctor x).obj Y) := by
  let : Finite (finiteEtalePointId x.residueField ⟶ (finiteEtaleBaseChange x.hom).obj Y) :=
    finite_hom_over_point x.residueField (finiteEtalePointId x.residueField)
      ((finiteEtaleBaseChange x.hom).obj Y)
  exact Finite.of_equiv _ (fiberPointHomEquiv x Y).symm

private lemma baseChange_isIso_of_fiber_isIso {X : Scheme.{u}} (x : GeometricPoint X)
    {A B : FiniteEtaleOver X} (f : A ⟶ B)
    [IsIso ((finiteEtaleFiberFunctor x).map f)] :
    IsIso ((finiteEtaleBaseChange x.hom).map f) := by
  let E := pointEquivFin x.residueField
  let : E.functor.IsEquivalence := E.isEquivalence_functor
  have : (E.functor ⋙ FintypeCat.incl).ReflectsIsomorphisms := inferInstance
  let : (coyoneda.obj (Opposite.op (finiteEtalePointId x.residueField))).ReflectsIsomorphisms :=
    reflectsIsomorphisms_of_iso (pointCoyonedaIso x.residueField).symm
  have : IsIso ((finiteEtaleBaseChange x.hom ⋙
      coyoneda.obj (Opposite.op (finiteEtalePointId x.residueField))).map f) :=
    (NatIso.isIso_map_iff (fiberIsoPointCoyoneda x) f).mp inferInstance
  have : IsIso ((coyoneda.obj (Opposite.op (finiteEtalePointId x.residueField))).map
      ((finiteEtaleBaseChange x.hom).map f)) := by
    change IsIso ((finiteEtaleBaseChange x.hom ⋙
      coyoneda.obj (Opposite.op (finiteEtalePointId x.residueField))).map f)
    infer_instance
  exact isIso_of_reflects_iso _
    (coyoneda.obj (Opposite.op (finiteEtalePointId x.residueField)))

private lemma baseChange_left_isPullback {X : Scheme.{u}} (x : GeometricPoint X)
    {A B : FiniteEtaleOver X} (f : A ⟶ B) :
    IsPullback ((finiteEtaleBaseChange x.hom).map f).left
      (pullback.fst A.hom x.hom) (pullback.fst B.hom x.hom) f.left := by
  let g := ((finiteEtaleBaseChange x.hom).map f).left
  have hsnd : g ≫ pullback.snd B.hom x.hom = pullback.snd A.hom x.hom := by
    simp only [g, finiteEtaleBaseChange, MorphismProperty.Over.pullback_map_left]
    exact pullback.lift_snd _ _ _
  have hfst : g ≫ pullback.fst B.hom x.hom = pullback.fst A.hom x.hom ≫ f.left := by
    simp only [g, finiteEtaleBaseChange, MorphismProperty.Over.pullback_map_left]
    exact pullback.lift_fst _ _ _
  have houter : IsPullback (g ≫ pullback.snd B.hom x.hom)
      (pullback.fst A.hom x.hom) x.hom (f.left ≫ B.hom) := by
    rw [hsnd, MorphismProperty.Over.w f]
    exact (IsPullback.of_hasPullback A.hom x.hom).flip
  exact houter.of_right hfst (IsPullback.of_hasPullback B.hom x.hom).flip

/-- A morphism of finite étale covers of `X` is finite and étale. -/
private lemma finite_etale_left {X : Scheme.{u}} {A B : FiniteEtaleOver X} (f : A ⟶ B) :
    IsFinite f.left ∧ Etale f.left := by
  have : IsFinite B.hom := B.prop.1
  have : Etale B.hom := B.prop.2
  have hfin : IsFinite (f.left ≫ B.hom) := by
    rw [MorphismProperty.Over.w f]
    exact A.prop.1
  have het : Etale (f.left ≫ B.hom) := by
    rw [MorphismProperty.Over.w f]
    exact A.prop.2
  exact ⟨IsFinite.of_comp f.left B.hom, Etale.of_comp f.left B.hom⟩

/-- A morphism of finite étale covers whose underlying morphism of schemes is an isomorphism is an
isomorphism. -/
private lemma isIso_of_isIso_left {X : Scheme.{u}} {A B : FiniteEtaleOver X} (f : A ⟶ B)
    [IsIso f.left] : IsIso f := by
  let e : A ≅ B := MorphismProperty.Over.isoMk (asIso f.left) (MorphismProperty.Over.w f)
  have he : e.hom = f := MorphismProperty.Over.Hom.ext rfl
  rw [← he]
  infer_instance

/-- A finite étale cover of a connected scheme has finitely many connected components. -/
private lemma finite_connectedComponents_left {X : Scheme.{u}} [ConnectedSpace X]
    (x : GeometricPoint X) (Y : FiniteEtaleOver X) : Finite (ConnectedComponents Y.left) := by
  have hYfin : IsFinite Y.hom := Y.prop.1
  have hYet : Etale Y.hom := Y.prop.2
  have : ConnectedSpace ((Functor.fromPUnit X).obj Y.right) := by
    change ConnectedSpace X
    infer_instance
  exact Y.hom.isOpenMap.finite_connectedComponents_of_finite_preimage_singleton_of_connectedSpace
    Y.hom.isClosedMap (Y.hom.finite_preimage_singleton (x.hom default))

private lemma mono_finiteEtale_isOpenImmersion {X : Scheme.{u}}
    {A B : FiniteEtaleOver X} (f : A ⟶ B) [Mono f] : IsOpenImmersion f.left := by
  let : Mono ((finiteEtaleOverForgetOver X).map f) := preserves_mono_of_preservesLimit _ f
  let : Mono f.left := CategoryTheory.Over.mono_left_of_mono
    ((finiteEtaleOverForgetOver X).map f)
  let : Etale f.left := (finite_etale_left f).2
  exact IsOpenImmersion.of_flat_of_mono f.left

private def finiteEtaleIsInitialOfIsEmpty {X : Scheme.{u}} (A : FiniteEtaleOver X)
    [IsEmpty A.left] : IsInitial A := by
  let hA : IsInitial A.left := AlgebraicGeometry.isInitialOfIsEmpty
  exact IsInitial.ofUniqueHom
    (fun B => MorphismProperty.Over.homMk (hA.to B.left) (by apply hA.hom_ext))
    fun B f => MorphismProperty.Over.Hom.ext (hA.hom_ext _ _)

private lemma finiteEtale_mono_iso_of_connected {X : Scheme.{u}} {A B : FiniteEtaleOver X}
    [ConnectedSpace B.left] (f : A ⟶ B) [Mono f] (hA : IsInitial A → False) : IsIso f := by
  have hne : Nonempty A.left := by
    by_contra h
    let : IsEmpty A.left := ⟨fun a => h ⟨a⟩⟩
    exact hA (finiteEtaleIsInitialOfIsEmpty A)
  let : IsFinite B.hom := B.prop.1
  let : IsSeparated B.hom := inferInstance
  let : IsFinite f.left := (finite_etale_left f).1
  let : IsOpenImmersion f.left := mono_finiteEtale_isOpenImmersion f
  have hclopen : IsClopen (Set.range f.left) :=
    ⟨f.left.isClosedMap.isClosed_range, f.left.isOpenMap.isOpen_range⟩
  have hrange : Set.range f.left = Set.univ :=
    hclopen.eq_univ ⟨f.left (Classical.choice hne), Classical.choice hne, rfl⟩
  have : IsIso f.left :=
    (AlgebraicGeometry.isIso_iff_isOpenImmersion_and_surjective f.left).2
      ⟨inferInstance, ⟨Set.range_eq_univ.mp hrange⟩⟩
  exact isIso_of_isIso_left f

/-- The empty scheme, as the initial finite étale cover of `X`. -/
private def finiteEtaleEmpty (X : Scheme.{u}) : FiniteEtaleOver X :=
  MorphismProperty.Over.mk ⊤ (Scheme.emptyTo X) ⟨inferInstance, inferInstance⟩

private lemma finiteEtale_connected {X : Scheme.{u}} (B : FiniteEtaleOver X)
    [ConnectedSpace B.left] [Nonempty B.left] : PreGaloisCategory.IsConnected B where
  notInitial h := by
    have h0 : IsEmpty ↥(finiteEtaleEmpty X).left := by
      change IsEmpty ↥(∅ : Scheme.{u})
      infer_instance
    let i : B ≅ finiteEtaleEmpty X :=
      h.uniqueUpToIso (finiteEtaleIsInitialOfIsEmpty (finiteEtaleEmpty X))
    have hempty : IsEmpty B.left := Function.isEmpty (fun b => i.hom.left b)
    exact isEmptyElim (Classical.choice (inferInstance : Nonempty B.left))
  noTrivialComponent A f hm hA := by
    let : Mono f := hm
    exact finiteEtale_mono_iso_of_connected f hA


private lemma finiteEtale_components {X : Scheme.{u}} [ConnectedSpace X]
    (x : GeometricPoint X) (Y : FiniteEtaleOver X) :
    ∃ (ι : Type) (A : ι → FiniteEtaleOver X) (f : (i : ι) → A i ⟶ Y)
      (_ : IsColimit (Cofan.mk Y f)),
      Finite ι ∧ ∀ i, PreGaloisCategory.IsConnected (A i) := by
  classical
  have hYfin : IsFinite Y.hom := Y.prop.1
  have hYet : Etale Y.hom := Y.prop.2
  have := finite_connectedComponents_left x Y
  let _ft : Fintype (ConnectedComponents Y.left) := Fintype.ofFinite _
  let e : Fin (Fintype.card (ConnectedComponents Y.left)) ≃ ConnectedComponents Y.left :=
    (Fintype.equivFin _).symm
  let z (c : ConnectedComponents Y.left) : Y.left :=
    Classical.choose (ConnectedComponents.surjective_coe c)
  let U (c : ConnectedComponents Y.left) : Y.left.Opens :=
    ⟨connectedComponent (z c), (isClopen_connectedComponent_of_finite (z c)).isOpen⟩
  let A (i : Fin (Fintype.card (ConnectedComponents Y.left))) : FiniteEtaleOver X := by
    have hc : IsClosed (U (e i) : Set Y.left) :=
      (isClopen_connectedComponent_of_finite (z (e i))).isClosed
    have : IsClosedImmersion (U (e i)).ι :=
      IsClosedImmersion.of_isPreimmersion _ (by
        simpa only [Scheme.Opens.range_ι] using hc)
    exact MorphismProperty.Over.mk ⊤ ((U (e i)).ι ≫ Y.hom) ⟨inferInstance, inferInstance⟩
  let f (i : Fin (Fintype.card (ConnectedComponents Y.left))) : A i ⟶ Y :=
    MorphismProperty.Over.homMk (U (e i)).ι (by rfl)
  have hc (i : Fin (Fintype.card (ConnectedComponents Y.left))) :
      PreGaloisCategory.IsConnected (A i) := by
    have : ConnectedSpace (A i).left :=
      isConnected_iff_connectedSpace.mp (by
        change _root_.IsConnected (connectedComponent (z (e i)))
        exact isConnected_connectedComponent)
    have : Nonempty (A i).left := ⟨⟨z (e i), mem_connectedComponent⟩⟩
    exact finiteEtale_connected (A i)
  have hcol : IsColimit (Cofan.mk Y f) := by
    have hscheme : IsColimit (Cofan.mk Y.left (fun i => (f i).left)) := by
      have hoi (i : Fin (Fintype.card (ConnectedComponents Y.left))) :
          IsOpenImmersion (f i).left := by
        change IsOpenImmersion (U (e i)).ι
        infer_instance
      have heq (i : Fin (Fintype.card (ConnectedComponents Y.left))) :
          (f i).left.opensRange = U (e i) :=
        TopologicalSpace.Opens.ext (Scheme.Opens.range_ι (U (e i)))
      apply (nonempty_isColimit_cofanMk_of (fun i => (f i).left) ?_ ?_).some
      · ext y
        simp_rw [heq]
        simp only [TopologicalSpace.Opens.coe_iSup,
          TopologicalSpace.Opens.coe_top, Set.mem_iUnion, Set.mem_univ, iff_true]
        refine ⟨e.symm (ConnectedComponents.mk y), ?_⟩
        change y ∈ connectedComponent (z (e (e.symm (ConnectedComponents.mk y))))
        rw [e.apply_symm_apply]
        have h := Classical.choose_spec
          (ConnectedComponents.surjective_coe (ConnectedComponents.mk y))
        exact (ConnectedComponents.coe_eq_coe').1 h.symm
      · intro i j hij
        change Disjoint (f i).left.opensRange (f j).left.opensRange
        rw [heq, heq]
        apply (TopologicalSpace.Opens.coe_disjoint (s := U (e i)) (t := U (e j))).mp
        rw [Set.disjoint_left]
        intro y hyc hyd
        have hcy : ConnectedComponents.mk y = e i := by
          have h := Classical.choose_spec (ConnectedComponents.surjective_coe (e i))
          rw [← h]
          exact (ConnectedComponents.coe_eq_coe').2 hyc
        have hdy : ConnectedComponents.mk y = e j := by
          have h := Classical.choose_spec (ConnectedComponents.surjective_coe (e j))
          rw [← h]
          exact (ConnectedComponents.coe_eq_coe').2 hyd
        exact hij (e.injective (hcy.symm.trans hdy))
    have hmap : IsColimit ((finiteEtaleOverForget X).mapCocone (Cofan.mk Y f)) :=
      (Cofan.isColimitMapCoconeEquiv (finiteEtaleOverForget X) A (Cofan.mk Y f)).symm hscheme
    exact Stacks.FundamentalGroup.isColimitOfIsColimitCoconeLeft (Cofan.mk Y f) hmap
  exact ⟨Fin (Fintype.card (ConnectedComponents Y.left)), A, f, hcol, inferInstance, hc⟩


private lemma fiber_reflectsIsomorphisms {X : Scheme.{u}} [ConnectedSpace X]
    (x : GeometricPoint X) : (finiteEtaleFiberFunctor x).ReflectsIsomorphisms := by
  refine ⟨fun {A B} f hf => ?_⟩
  have hA1 : IsFinite A.hom := A.prop.1
  have hB1 : IsFinite B.hom := B.prop.1
  have hA2 : Etale A.hom := A.prop.2
  have hB2 : Etale B.hom := B.prop.2
  have hfl : IsFinite f.left := (finite_etale_left f).1
  have hfe : Etale f.left := (finite_etale_left f).2
  let g := (finiteEtaleBaseChange x.hom).map f
  have hg : IsIso g := baseChange_isIso_of_fiber_isIso x f
  have hgl : IsIso g.left := (inferInstance : IsIso ((finiteEtaleOverForget x.source).map g))
  have := finite_connectedComponents_left x B
  let _cs : ConnectedSpace ((Functor.fromPUnit X).obj B.right) := by
    change ConnectedSpace X
    infer_instance
  have hrank : f.left.finrank = 1 := by
    ext b
    have hcl : IsClopen (connectedComponent b) := isClopen_connectedComponent_of_finite b
    have hclImage : IsClopen (B.hom '' connectedComponent b) :=
      ⟨B.hom.isClosedMap _ hcl.isClosed, B.hom.isOpenMap _ hcl.isOpen⟩
    have himage : B.hom '' connectedComponent b = Set.univ :=
      hclImage.eq_univ ⟨B.hom b, b, mem_connectedComponent, rfl⟩
    have hmem : x.hom default ∈ B.hom '' connectedComponent b := by
      rw [himage]
      trivial
    obtain ⟨b₀, hb₀, hbmap⟩ := hmem
    obtain ⟨q, hqfst, _⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := B.hom) (g := x.hom) b₀ default hbmap
    have hpb := baseChange_left_isPullback x f
    have heq : g.left.finrank q = f.left.finrank b₀ := by
      have h := Scheme.Hom.finrank_of_isPullback
        (pullback.fst A.hom x.hom) g.left f.left (pullback.fst B.hom x.hom) hpb.flip q
      exact h.trans (congrArg (Scheme.Hom.finrank f.left) hqfst)
    have hrank₀ : f.left.finrank b₀ = 1 := by
      rw [← heq]
      exact congrFun (Scheme.Hom.finrank_eq_one_of_isIso g.left) q
    have hlocal : IsLocallyConstant f.left.finrank := f.left.isLocallyConstant_finrank
    exact (hlocal.apply_eq_of_isPreconnected
      isConnected_connectedComponent.isPreconnected mem_connectedComponent hb₀).trans hrank₀
  have : IsIso f.left := (Scheme.Hom.isIso_iff_finrank_eq f.left).2 hrank
  exact isIso_of_isIso_left f

/-! ### The Galois-category axioms that hold unconditionally -/

/-- **The geometric fibres of a finite étale cover are finite.** For a geometric point `x` of a
scheme `X` and a finite étale cover `Y ⟶ X`, the set of lifts of `x` to `Y` is finite: base
changing to `x` turns those lifts into sections of a finite étale cover of the spectrum of a
separably closed field, and there are finitely many of those because such covers are equivalent
to finite sets.

This is the `finite_obj` axiom of `CategoryTheory.IsGaloisCategory` for the geometric
fibre functor, and it is exactly the hypothesis that the conditional profiniteness instances of
`AlgebraicGeometry.EtaleFundamentalGroup` take, so it makes `π₁(X, x)` profinite. -/
@[sga "4½ Arcata 2.4.2" "more general"]
alias finite_finiteEtaleFiber := fiber_finite

/-- Finiteness of every geometric fibre, in the `∀`-shape in which the conditional
profiniteness instances of `AlgebraicGeometry.EtaleFundamentalGroup` take it as a hypothesis.
`have := forall_finite_finiteEtaleFiberFunctor_obj x` makes those instances fire. -/
theorem forall_finite_finiteEtaleFiberFunctor_obj {X : Scheme.{u}} (x : GeometricPoint X) :
    ∀ Y, Finite ((finiteEtaleFiberFunctor x).obj Y) :=
  fun Y ↦ fiber_finite x Y

/-- **Stacks 0BMR for the étale fundamental group: `π₁(X, x)` is compact**, unconditionally.
The conditional instance `AlgebraicGeometry.etaleFundamentalGroupCompactSpace` asks for
finiteness of the geometric fibres, which `AlgebraicGeometry.finite_finiteEtaleFiber`
supplies. -/
theorem compactSpace_etaleFundamentalGroup (X : Scheme.{u}) [ConnectedSpace X]
    (x : GeometricPoint X) : CompactSpace (EtaleFundamentalGroup X x) := by
  have := forall_finite_finiteEtaleFiberFunctor_obj x
  exact etaleFundamentalGroupCompactSpace X x

/-- **Stacks 0BMR for the étale fundamental group: `π₁(X, x)` is Hausdorff**,
unconditionally. -/
theorem t2Space_etaleFundamentalGroup (X : Scheme.{u}) [ConnectedSpace X]
    (x : GeometricPoint X) : T2Space (EtaleFundamentalGroup X x) := by
  have := forall_finite_finiteEtaleFiberFunctor_obj x
  exact etaleFundamentalGroupT2Space X x

/-- **Stacks 0BMR for the étale fundamental group: `π₁(X, x)` is totally disconnected**,
unconditionally. Together with the previous two results, `π₁(X, x)` is profinite. -/
theorem totallyDisconnectedSpace_etaleFundamentalGroup (X : Scheme.{u}) [ConnectedSpace X]
    (x : GeometricPoint X) : TotallyDisconnectedSpace (EtaleFundamentalGroup X x) := by
  have := forall_finite_finiteEtaleFiberFunctor_obj x
  exact etaleFundamentalGroupTotallyDisconnectedSpace X x

/-- The geometric fibre functor preserves finite limits. It is isomorphic to the functor
corepresented by the geometric point in the category of schemes over `X`, and the forgetful
functor to that category preserves finite limits. -/
alias preservesFiniteLimits_finiteEtaleFiberFunctor := fiber_preservesFiniteLimits

/-- The geometric fibre functor of a connected scheme reflects isomorphisms. A morphism of finite
étale covers whose fibre map is bijective has degree one on the component of the geometric point,
hence degree one everywhere by connectedness, hence is an isomorphism. -/
@[sga "3 XVII 1.6" "Over k̄"]
alias reflectsIsomorphisms_finiteEtaleFiberFunctor := fiber_reflectsIsomorphisms

/-- **Every finite étale cover of a connected scheme is a finite coproduct of connected ones**,
namely of its connected components, which are finite in number because the structure morphism is
finite, open and closed. This is the `exists_finite_coproduct_connected` axiom of
`CategoryTheory.IsGaloisCategory`. -/
alias exists_finiteCoproduct_isConnected_finiteEtaleOver := finiteEtale_components

end AlgebraicGeometry
end
