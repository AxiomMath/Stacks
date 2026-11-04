module

public import StacksFrontier.AlgebraicGeometry.Descent.BigHRingSheafSystemDescentIso

/-!
# Recognising the canonical descent datum of a module: the assembly

`StacksFrontier.AlgebraicGeometry.Descent.BigHRingSheafSystemDescentIso` proves, for a system of
sheaves of rings `𝓡` on the big h category over `S`, the compatibility of the restrictions of a
module `G` with the gluing morphisms of a descent datum over one fibre product
(`AlgebraicGeometry.BigHOver.RingSheafSystem.comm_toDescentData`). This file assembles those
compatibilities into an isomorphism of descent data, and supplies the chosen fibre products of two
opens of an object of the site that a family of opens is glued along.

## Main definitions

* `CategoryTheory.Pseudofunctor.DescentData.isoMkOfChosenPullback` and
  `CategoryTheory.Pseudofunctor.DescentData.toDescentDataIsoOfChosenPullback`: isomorphisms of
  descent data from compatibilities over chosen fibre products, for an arbitrary pseudofunctor.
* `AlgebraicGeometry.BigHOver.opensChosenPullback`: the intersection of two opens of an object of
  `(Sch/S)_h` as a chosen fibre product of their inclusions.
* `AlgebraicGeometry.BigHOver.RingSheafSystem.toDescentDataIsoOfHomEquiv`: **recognising the
  canonical descent datum of a module** from isomorphisms of components whose transposes are
  compatible with the gluing morphisms.

## Implementation notes

The assembly is stated first for an arbitrary pseudofunctor and only then instantiated at the
pseudofunctor of modules of `𝓡`: elaborating `CategoryTheory.Pseudofunctor.DescentData.isoMk`
directly at the concrete pseudofunctor unfolds its fibres, which are categories of sheaves of
modules, and times out.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace CategoryTheory.Pseudofunctor.DescentData

universe t v' u' v u₀

variable {C : Type u₀} [Category.{v} C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
  {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}

/-- **An isomorphism of descent data from isomorphisms of components compatible over chosen fibre
products.** `CategoryTheory.Pseudofunctor.DescentData.isoMk` asks for the compatibility over
every object mapping to two members of the family; by
`CategoryTheory.Pseudofunctor.DescentData.comm_of_chosenPullback` it suffices over chosen fibre
products. -/
def isoMkOfChosenPullback {D₁ D₂ : F.DescentData f} (sq : ∀ i₁ i₂, ChosenPullback (f i₁) (f i₂))
    (e : ∀ i, D₁.obj i ≅ D₂.obj i)
    (comm : ∀ i₁ i₂,
      (F.map (sq i₁ i₂).p₁.op.toLoc).toFunctor.map (e i₁).hom ≫
          D₂.hom (sq i₁ i₂).p (sq i₁ i₂).p₁ (sq i₁ i₂).p₂ =
        D₁.hom (sq i₁ i₂).p (sq i₁ i₂).p₁ (sq i₁ i₂).p₂ ≫
          (F.map (sq i₁ i₂).p₂.op.toLoc).toFunctor.map (e i₂).hom) :
    D₁ ≅ D₂ :=
  isoMk e (fun _ q _ _ a₁ a₂ ha₁ ha₂ =>
    comm_of_chosenPullback sq (fun i => (e i).hom) comm q a₁ a₂ ha₁ ha₂)

/-- **An isomorphism from the canonical descent datum of an object**, from isomorphisms between
the restrictions of the object and the components of a descent datum, compatible over chosen fibre
products. This is `CategoryTheory.Pseudofunctor.DescentData.isoMkOfChosenPullback` with the first
descent datum `F.toDescentData f` applied to the object, its components being typed as
restrictions. -/
def toDescentDataIsoOfChosenPullback (D : F.DescentData f)
    (sq : ∀ i₁ i₂, ChosenPullback (f i₁) (f i₂)) (G : F.obj (.mk (op S)))
    (e : ∀ i, (F.map (f i).op.toLoc).toFunctor.obj G ≅ D.obj i)
    (comm : ∀ i₁ i₂,
      (F.map (sq i₁ i₂).p₁.op.toLoc).toFunctor.map (e i₁).hom ≫
          D.hom (sq i₁ i₂).p (sq i₁ i₂).p₁ (sq i₁ i₂).p₂ =
        ((F.toDescentData f).obj G).hom (sq i₁ i₂).p (sq i₁ i₂).p₁ (sq i₁ i₂).p₂ ≫
          (F.map (sq i₁ i₂).p₂.op.toLoc).toFunctor.map (e i₂).hom) :
    (F.toDescentData f).obj G ≅ D :=
  isoMkOfChosenPullback sq e comm

end CategoryTheory.Pseudofunctor.DescentData

namespace AlgebraicGeometry.BigHOver

universe u

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The intersection of two opens of an object of `(Sch/S)_h` is their fibre product**, as a
chosen pullback of the two inclusions in the site. -/
def opensChosenPullback {X : BigHOver B S hS} (V W : ((toScheme B S hS).obj X).Opens) :
    ChosenPullback (opensι B S hS V) (opensι B S hS W) where
  pullback := opensObj B S hS (V ⊓ W)
  p₁ := opensHom B S hS inf_le_left
  p₂ := opensHom B S hS inf_le_right
  condition := by rw [opensHom_opensι, opensHom_opensι]
  isLimit := (IsPullback.of_map (toScheme B S hS)
    (f := opensHom B S hS (inf_le_left : V ⊓ W ≤ V))
    (g := opensHom B S hS (inf_le_right : V ⊓ W ≤ W))
    (h := opensι B S hS V) (i := opensι B S hS W)
    (by rw [opensHom_opensι, opensHom_opensι]) (isPullback_opens_inf V W)).isLimit
  p := opensι B S hS (V ⊓ W)
  hp₁ := opensHom_opensι B S hS inf_le_left

end AlgebraicGeometry.BigHOver

namespace AlgebraicGeometry.BigHOver.RingSheafSystem

universe u

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (𝓡 : RingSheafSystem B S hS)

/-- **Recognising the canonical descent datum of a module.** Isomorphisms `e i` between the
restrictions of a module `G` and the components of a descent datum `D` assemble into an
isomorphism of descent data, as soon as their transposes are compatible with the gluing
morphisms of `D` over chosen fibre products. -/
def toDescentDataIsoOfHomEquiv {ι' : Type u} {U : BigHOver B S hS} {X : ι' → BigHOver B S hS}
    {f : ∀ i, X i ⟶ U} (D : 𝓡.modulePseudofunctor.DescentData f)
    (sq : ∀ i j, ChosenPullback (f i) (f j)) (G : 𝓡.modulePseudofunctor.obj ⟨op U⟩)
    (e : ∀ i, (𝓡.modulePseudofunctor.map (f i).op.toLoc).toFunctor.obj G ≅ D.obj i)
    (hyp : ∀ i j, (𝓡.adj (f i)).homEquiv G (D.obj i) (e i).hom ≫
        𝓡.etaG (sq i j).p₁ (f i) (sq i j).p (sq i j).hp₁ (D.obj i) ≫
          (𝓡.push (sq i j).p).map
            (D.hom (sq i j).p (sq i j).p₁ (sq i j).p₂ (sq i j).hp₁ (sq i j).hp₂) =
      (𝓡.adj (f j)).homEquiv G (D.obj j) (e j).hom ≫
        𝓡.etaG (sq i j).p₂ (f j) (sq i j).p (sq i j).hp₂ (D.obj j)) :
    (𝓡.modulePseudofunctor.toDescentData f).obj G ≅ D :=
  Pseudofunctor.DescentData.toDescentDataIsoOfChosenPullback D sq G e (fun i j =>
    𝓡.comm_toDescentData f D G (sq i j).p (sq i j).p₁ (sq i j).p₂ (sq i j).hp₁ (sq i j).hp₂
      (e i).hom (e j).hom (hyp i j))

/-- The components of `AlgebraicGeometry.BigHOver.RingSheafSystem.toDescentDataIsoOfHomEquiv` are
the given isomorphisms. -/
@[simp]
lemma toDescentDataIsoOfHomEquiv_hom_hom {ι' : Type u} {U : BigHOver B S hS}
    {X : ι' → BigHOver B S hS} {f : ∀ i, X i ⟶ U} (D : 𝓡.modulePseudofunctor.DescentData f)
    (sq : ∀ i j, ChosenPullback (f i) (f j)) (G : 𝓡.modulePseudofunctor.obj ⟨op U⟩)
    (e : ∀ i, (𝓡.modulePseudofunctor.map (f i).op.toLoc).toFunctor.obj G ≅ D.obj i)
    (hyp : ∀ i j, (𝓡.adj (f i)).homEquiv G (D.obj i) (e i).hom ≫
        𝓡.etaG (sq i j).p₁ (f i) (sq i j).p (sq i j).hp₁ (D.obj i) ≫
          (𝓡.push (sq i j).p).map
            (D.hom (sq i j).p (sq i j).p₁ (sq i j).p₂ (sq i j).hp₁ (sq i j).hp₂) =
      (𝓡.adj (f j)).homEquiv G (D.obj j) (e j).hom ≫
        𝓡.etaG (sq i j).p₂ (f j) (sq i j).p (sq i j).hp₂ (D.obj j)) (i : ι') :
    (𝓡.toDescentDataIsoOfHomEquiv D sq G e hyp).hom.hom i = (e i).hom :=
  rfl

end AlgebraicGeometry.BigHOver.RingSheafSystem

end
