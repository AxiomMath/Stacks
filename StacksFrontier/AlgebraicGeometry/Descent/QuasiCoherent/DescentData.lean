module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.CategoryTheory.Sites.Hypercover.ZeroOver
public import StacksCore.Tactic.StacksAttribute

/-!
# Descent data for quasi-coherent sheaves

For a family of morphisms of schemes with common target, a descent datum consists of a
quasicoherent sheaf on each source and compatible identifications after pullback.  Morphisms are
families of morphisms of sheaves commuting with these identifications.  A morphism of families
with fixed target pulls such a datum back, and every quasicoherent module on the target carries a
canonical datum, obtained by pulling back the trivial datum on the singleton identity family.  A
datum is *effective* when it is isomorphic to a canonical one.

## Main definitions

* `AlgebraicGeometry.modulePullbackPseudofunctor` is the contravariant pseudofunctor of sheaves
  of modules on schemes.
* `AlgebraicGeometry.QuasicoherentDescentData` is the category of descent data whose component
  sheaves are quasicoherent.
* `AlgebraicGeometry.QuasicoherentDescentData.pullFunctor` is the pullback functor on
  quasicoherent descent data.
* `AlgebraicGeometry.canonicalDescentFunctor` sends a quasicoherent module to its canonical
  descent datum.
* `AlgebraicGeometry.trivialDescentData` is the canonical datum for the singleton identity
  family, and `AlgebraicGeometry.trivialDescentComponentIso` identifies its sole component with
  the original module.
* `AlgebraicGeometry.QuasicoherentDescentData.IsEffective` says that a datum is isomorphic to a
  canonical one.

## Main results

* `AlgebraicGeometry.QuasicoherentDescentData.pullFunctor_comp_ι` identifies the underlying
  functor of `pullFunctor` with the usual pullback functor on descent data.
* `AlgebraicGeometry.QuasicoherentDescentData.pullFunctorIsoOfEq`: two morphisms of families
  inducing the same morphism of targets give naturally isomorphic pullback functors.
* `AlgebraicGeometry.pullTrivialDescentIso` identifies the canonical datum with the pullback of
  the trivial datum along the given family, naturally in the module.
* `AlgebraicGeometry.trivialDescentData_hom_self` identifies every transition of the trivial
  datum with the identity.

## Implementation notes

The underlying descent datum is Mathlib's invariant `Pseudofunctor.DescentData`: its transition
isomorphisms are available over every common pullback.  After choosing binary and triple fibre
products, `Pseudofunctor.DescentData'.descentDataEquivalence` identifies this category with the
source's presentation by transition isomorphisms on binary fibre products satisfying the cocycle
condition on triple fibre products.  Both functors in this equivalence preserve the component
sheaves, so they identify the full subcategories on quasicoherent components and their morphisms.
We use the invariant side to avoid choices of fibre products and retain its existing API.

Quasicoherence of the components of a pullback is Stacks 01BG, in the scheme-level form
`Stacks.Modules.isQuasicoherent_pullback`.  Functoriality is retained by defining the whole
canonical-descent functor, rather than only its value on an object.  The trivial datum is its
specialization to the singleton family consisting of the identity; its component is naturally
isomorphic to the original module via the unit comparison of the pullback pseudofunctor, and its
transitions are identities by `trivialDescentData_hom_self`.  The morphism from an arbitrary
family to this singleton family pulls the trivial datum back to the canonical one, which is
`pullTrivialDescentIso`.  Effectivity is membership in the essential image of the canonical
descent functor, which is precisely the existence of a quasicoherent module together with an
isomorphism from its canonical datum; its essential-image API supplies witnesses, their
isomorphisms, and invariance under isomorphism directly.

## References

* [Stacks Project, Tag 023B](https://stacks.math.columbia.edu/tag/023B)
* [Stacks Project, Tag 023C](https://stacks.math.columbia.edu/tag/023C)
* [Stacks Project, Tag 023D](https://stacks.math.columbia.edu/tag/023D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

universe w' w v u

namespace AlgebraicGeometry

/-- The contravariant pseudofunctor sending a scheme to its category of sheaves of modules and a
morphism of schemes to pullback. -/
@[implicit_reducible]
noncomputable def modulePullbackPseudofunctor :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  Scheme.Modules.pseudofunctor.comp Bicategory.Adj.forget₁

/-- Descent data for quasicoherent sheaves relative to a family `f i : X i ⟶ S`.

The underlying descent datum supplies the transition isomorphisms and their cocycle condition.
Morphisms in this full subcategory are componentwise morphisms commuting with every transition
isomorphism.  For chosen binary and triple fibre products,
`Pseudofunctor.DescentData'.descentDataEquivalence` is component-preserving and identifies this
with the full subcategory of the source's fibre-product presentation on quasicoherent objects. -/
@[stacks 023B]
abbrev QuasicoherentDescentData {I : Type v} {S : Scheme.{u}} {X : I → Scheme.{u}}
    (f : ∀ i, X i ⟶ S) :=
  (show ObjectProperty (modulePullbackPseudofunctor.DescentData f) from
    fun D => ∀ i, (D.obj i).IsQuasicoherent).FullSubcategory

namespace QuasicoherentDescentData

variable {I : Type v} {S : Scheme.{u}} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ S}

/-- The quasicoherent sheaf at one member of the family. -/
abbrev component (D : QuasicoherentDescentData f) (i : I) : (X i).Modules := D.obj.obj i

instance (D : QuasicoherentDescentData f) (i : I) : (D.component i).IsQuasicoherent :=
  D.property i

section Pull

variable {U V : Scheme.{u}} {𝒰 : PreZeroHypercover.{w} U} {𝒱 : PreZeroHypercover.{w'} V}
  {g : U ⟶ V}

/-- Pullback along a morphism of families defines a functor on quasicoherent descent data.

Its underlying functor is `Pseudofunctor.DescentData.pullFunctor`; quasicoherence of its
components follows from preservation of quasicoherence by pullback. -/
@[stacks 023C "part (2), the pullback functor"]
noncomputable def pullFunctor (Φ : 𝒰.HomOver 𝒱 g) :
    QuasicoherentDescentData 𝒱.f ⥤ QuasicoherentDescentData 𝒰.f :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙
      Pseudofunctor.DescentData.pullFunctor modulePullbackPseudofunctor
        (f := 𝒱.f) (p := g) (f' := 𝒰.f) (α := Φ.s₀) (p' := Φ.h₀) Φ.w₀)
    fun D i ↦ Stacks.Modules.isQuasicoherent_pullback (Φ.h₀ i) _ (D.property (Φ.s₀ i))

/-- After forgetting quasicoherence, `pullFunctor` is exactly the usual pullback functor on
descent data.  Thus its objects have components `g_i^* F_{α(i)}` and the pulled-back transition
isomorphisms, and its action on morphisms is componentwise pullback. -/
@[stacks 023C "part (1), the pulled-back descent datum"]
theorem pullFunctor_comp_ι (Φ : 𝒰.HomOver 𝒱 g) :
    pullFunctor Φ ⋙ ObjectProperty.ι _ = ObjectProperty.ι _ ⋙
        Pseudofunctor.DescentData.pullFunctor modulePullbackPseudofunctor
          (f := 𝒱.f) (p := g) (f' := 𝒰.f) (α := Φ.s₀) (p' := Φ.h₀) Φ.w₀ :=
  CategoryTheory.Functor.ext fun _ ↦ rfl

/-- Morphisms of families inducing the same morphism of targets give naturally isomorphic
pullback functors on quasicoherent descent data. -/
@[stacks 023C "part (3), functorial isomorphism when the maps of targets agree"]
noncomputable def pullFunctorIsoOfEq {g' : U ⟶ V} (Φ : 𝒰.HomOver 𝒱 g)
    (Φ' : 𝒰.HomOver 𝒱 g') (h : g = g') : pullFunctor Φ ≅ pullFunctor Φ' := by
  subst h
  let e := Pseudofunctor.DescentData.pullFunctorIso modulePullbackPseudofunctor
    (f := 𝒱.f) (p := g) (f' := 𝒰.f) (α := Φ.s₀) (p' := Φ.h₀) Φ.w₀
    (β := Φ'.s₀) (p'' := Φ'.h₀) Φ'.w₀
  let ι𝒱 := ObjectProperty.ι (fun D : modulePullbackPseudofunctor.DescentData 𝒱.f ↦
    ∀ i, (D.obj i).IsQuasicoherent)
  exact NatIso.ofComponents
    (fun D ↦ (ObjectProperty.isoMk
      (P := fun D : modulePullbackPseudofunctor.DescentData 𝒰.f ↦
        ∀ i, (D.obj i).IsQuasicoherent)
      (e.app (ι𝒱.obj D)) : (pullFunctor Φ).obj D ≅ (pullFunctor Φ').obj D))
    fun φ ↦ by
      apply ObjectProperty.hom_ext
      exact e.hom.naturality (ι𝒱.map φ)

end Pull

end QuasicoherentDescentData

/-- The functor sending a quasicoherent module on `S` to its canonical descent datum relative to
the family `f i : X i ⟶ S`. -/
@[stacks 023D "part (2)", implicit_reducible, simps! obj_obj_obj map_hom_hom]
noncomputable def canonicalDescentFunctor {I : Type v} {S : Scheme.{u}}
    {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S) :
    Functor (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory
      (QuasicoherentDescentData f) :=
  ObjectProperty.lift
    (show ObjectProperty (modulePullbackPseudofunctor.DescentData f) from
      fun D ↦ ∀ i, (D.obj i).IsQuasicoherent)
    ((SheafOfModules.isQuasicoherent S.ringCatSheaf).ι ⋙
      modulePullbackPseudofunctor.toDescentData f)
    fun M i ↦ Stacks.Modules.isQuasicoherent_pullback (f i) M.obj M.property

/-- Forgetting quasicoherence identifies the canonical functor with the pseudofunctor's
canonical descent functor. -/
theorem canonicalDescentFunctor_comp_ι {I : Type v} {S : Scheme.{u}}
    {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S) :
    canonicalDescentFunctor f ⋙ ObjectProperty.ι _ =
      (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι ⋙
        modulePullbackPseudofunctor.toDescentData f := rfl

/-- The trivial descent datum on a quasicoherent module, relative to the singleton family whose
only morphism is the identity of the base scheme. -/
@[stacks 023D "part (1)"]
noncomputable abbrev trivialDescentData {S : Scheme.{u}}
    (M : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    QuasicoherentDescentData (PreZeroHypercover.singleton.{0} (𝟙 S)).f :=
  (canonicalDescentFunctor (PreZeroHypercover.singleton.{0} (𝟙 S)).f).obj M

attribute [local implicit_reducible] PreZeroHypercover.singleton in
/-- The functor taking a quasicoherent module to the sole component of its trivial descent
datum.  This component is the pullback of the module along the identity. -/
@[implicit_reducible]
noncomputable def trivialDescentComponentFunctor {S : Scheme.{u}} :
    Functor (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory
      (SheafOfModules.{u} S.ringCatSheaf) :=
  canonicalDescentFunctor (PreZeroHypercover.singleton.{0} (𝟙 S)).f ⋙
    ObjectProperty.ι _ ⋙
      { obj := fun D ↦ D.obj PUnit.unit
        map := fun φ ↦ φ.hom PUnit.unit }

/-- The sole component of the trivial descent datum is naturally isomorphic to the original
quasicoherent module. -/
@[stacks 023D "part (1), identity comparison"]
noncomputable def trivialDescentComponentIso {S : Scheme.{u}} :
    trivialDescentComponentFunctor (S := S) ≅
      (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι :=
  NatIso.ofComponents
    (fun M ↦ (Cat.Hom.toNatIso
      (modulePullbackPseudofunctor.mapId (.mk (.op S)))).app M.obj)
    fun φ ↦ (Cat.Hom.toNatIso
      (modulePullbackPseudofunctor.mapId (.mk (.op S)))).hom.naturality φ.hom

attribute [local implicit_reducible] PreZeroHypercover.singleton in
/-- The canonical morphism from a family to the singleton identity family.

This is `AlgebraicGeometry.QuasicoherentDescentData.toSingletonFamily` at `g = 𝟙 S`
without that definition's `Small.{u}` hypothesis on the index, which the one-element
family of a given morphism does not need. -/
@[implicit_reducible]
def toTrivialFamily {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{v} S) :
    𝒰.HomOver (PreZeroHypercover.singleton.{0} (𝟙 S)) (𝟙 S) where
  s₀ _ := PUnit.unit
  h₀ i := 𝒰.f i
  w₀ _ := Category.comp_id _

attribute [local implicit_reducible] PreZeroHypercover.singleton in
/-- The component of the trivial datum is canonically the original module: this is the
identity-pullback comparison.  See `trivialDescentDataComponentIso_naturality` for
naturality. -/
noncomputable def trivialDescentDataComponentIso {S : Scheme.{u}}
    (M : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    (trivialDescentData M).component PUnit.unit ≅ M.obj :=
  trivialDescentComponentIso.app M

attribute [local implicit_reducible] PreZeroHypercover.singleton in
/-- The identity-pullback comparison for the trivial datum is natural in the module. -/
theorem trivialDescentDataComponentIso_naturality {S : Scheme.{u}}
    {M N : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory} (φ : M ⟶ N) :
    ((canonicalDescentFunctor (PreZeroHypercover.singleton.{0} (𝟙 S)).f).map φ).hom.hom
        PUnit.unit ≫ (trivialDescentDataComponentIso N).hom =
      (trivialDescentDataComponentIso M).hom ≫ φ.hom :=
  trivialDescentComponentIso.hom.naturality φ

attribute [local implicit_reducible] PreZeroHypercover.singleton in
/-- Every transition of the trivial datum is an identity: over the identity family the two
maps to its sole member must agree, and the descent datum's `hom_self` applies. -/
@[simp]
theorem trivialDescentData_hom_self {S : Scheme.{u}}
    (M : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory)
    {Y : Scheme.{u}} (q : Y ⟶ S) :
    (trivialDescentData M).obj.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) q q
      (Category.comp_id q) (Category.comp_id q) = 𝟙 _ :=
  (trivialDescentData M).obj.hom_self q q (Category.comp_id q)

/-- The refinement from any family to the singleton identity family: the index map is the
unique map to its singleton index type, and the component maps are the given family. -/
abbrev identityFamilyRefinement {I : Type v} {S : Scheme.{u}}
    {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S) :
    (show PreZeroHypercover S from ⟨I, X, f⟩).HomOver
      (PreZeroHypercover.singleton.{0} (𝟙 S)) (𝟙 S) :=
  toTrivialFamily ⟨I, X, f⟩

/-- Forgetting quasicoherence identifies the pullback of the trivial descent functor along a
family with the pseudofunctor's.  This is the equality that `pullTrivialDescentIso` transports
the identity-pullback comparison along. -/
private lemma pullTrivialDescentFunctor_comp_ι {S : Scheme.{u}}
    (𝒰 : PreZeroHypercover.{v} S) :
    (canonicalDescentFunctor (PreZeroHypercover.singleton.{0} (𝟙 S)).f ⋙
      QuasicoherentDescentData.pullFunctor (toTrivialFamily 𝒰)) ⋙ ObjectProperty.ι _ =
      (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι ⋙
        (modulePullbackPseudofunctor.toDescentData
            (PreZeroHypercover.singleton.{0} (𝟙 S)).f ⋙
          Pseudofunctor.DescentData.pullFunctor modulePullbackPseudofunctor
            (toTrivialFamily 𝒰).w₀) := by
  rw [Functor.assoc, QuasicoherentDescentData.pullFunctor_comp_ι, ← Functor.assoc,
    canonicalDescentFunctor_comp_ι]
  exact Functor.assoc _ _ _

/-- Pulling the trivial descent datum back along a family gives, naturally in the
quasicoherent module, its canonical descent datum for that family. -/
@[stacks 023D "part (2), pullback of the trivial datum"]
noncomputable def pullTrivialDescentIso {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{v} S) :
    canonicalDescentFunctor (PreZeroHypercover.singleton.{0} (𝟙 S)).f ⋙
        QuasicoherentDescentData.pullFunctor (toTrivialFamily 𝒰) ≅
      canonicalDescentFunctor 𝒰.f := by
  apply Functor.fullyFaithfulCancelRight (ObjectProperty.ι _)
  exact eqToIso (by exact pullTrivialDescentFunctor_comp_ι 𝒰) ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι
      (Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso
          modulePullbackPseudofunctor (toTrivialFamily 𝒰).w₀ ≪≫
        Functor.isoWhiskerRight
          (Cat.Hom.toNatIso (modulePullbackPseudofunctor.mapId (.mk (.op S)))) _ ≪≫
        Functor.leftUnitor _) ≪≫
    eqToIso (by exact (canonicalDescentFunctor_comp_ι 𝒰.f).symm)

/-- Pulling back the trivial descent datum by the refinement to the identity family, using
the functor of 023C, gives the canonical descent datum.  This is a natural isomorphism in the
quasicoherent module, and its component at `M` compares the pullback of `trivialDescentData M`
with `(canonicalDescentFunctor f).obj M`, as required by part (2) of 023D. -/
noncomputable def trivialDescentFunctorCompPullFunctorIso {I : Type v} {S : Scheme.{u}}
    {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S) :
    canonicalDescentFunctor (PreZeroHypercover.singleton.{0} (𝟙 S)).f ⋙
        QuasicoherentDescentData.pullFunctor (identityFamilyRefinement f) ≅
      canonicalDescentFunctor f :=
  pullTrivialDescentIso ⟨I, X, f⟩

namespace QuasicoherentDescentData

variable {I : Type v} {S : Scheme.{u}} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ S}

/-- A quasicoherent descent datum is effective if it is isomorphic to the canonical descent
datum of a quasicoherent module on the target. -/
@[stacks 023D "part (3)", stacks 03O7 "the effectivity clause"]
abbrev IsEffective (D : QuasicoherentDescentData f) : Prop :=
  (canonicalDescentFunctor f).essImage D

end QuasicoherentDescentData

end AlgebraicGeometry
