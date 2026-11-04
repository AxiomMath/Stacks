module

public import Mathlib.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty
public import Mathlib.CategoryTheory.Sites.Descent.Precoverage
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.Effective

/-!
# Fpqc descent of quasi-coherent modules as a stack condition

Stacks 023T asserts that for an fpqc covering family `f i : X i ⟶ S` the canonical descent
functor `AlgebraicGeometry.canonicalDescentFunctor` on quasi-coherent modules is fully faithful
and every quasi-coherent descent datum is effective.  Both halves are statements about the full
subcategories on quasi-coherent objects, whereas Mathlib's descent API
(`CategoryTheory.Pseudofunctor.IsPrestack`, `CategoryTheory.Pseudofunctor.IsStack`) speaks about
a pseudofunctor as a whole.

This file removes that mismatch.  Quasi-coherence *is* a
`CategoryTheory.Pseudofunctor.ObjectProperty` of
`AlgebraicGeometry.modulePullbackPseudofunctor`, closed under the pullback functors by
Stacks 01BG, so Mathlib's `CategoryTheory.Pseudofunctor.ObjectProperty.fullsubcategory` produces
the pseudofunctor `Stacks.Descent.qcohPseudofunctor` of quasi-coherent modules.  Its category of
descent data is equivalent to `AlgebraicGeometry.QuasicoherentDescentData`, and its canonical
descent functor is `AlgebraicGeometry.canonicalDescentFunctor`.  Consequently **both** halves of
Stacks 023T follow from `qcohPseudofunctor.IsStack Scheme.fpqcTopology` with **no auxiliary
hypothesis** — in particular with no hypothesis that quasi-coherence descends along the family,
which `Stacks.Descent.isEffective_of_essImage` needs.  Stacks 023T is therefore reduced to that
one condition.

## Main definitions

* `Stacks.Descent.quasicoherentProperty`: quasi-coherence as a property of objects of
  `AlgebraicGeometry.modulePullbackPseudofunctor`.
* `Stacks.Descent.qcohPseudofunctor`: the pseudofunctor sending a scheme to its category of
  quasi-coherent modules and a morphism of schemes to pullback.
* `Stacks.Descent.descentDataForgetFunctor` and `Stacks.Descent.descentDataEquivalence`: the
  equivalence between the descent data of `qcohPseudofunctor` and
  `AlgebraicGeometry.QuasicoherentDescentData`.
* `Stacks.Descent.homMk`: a morphism of descent data for `qcohPseudofunctor` from morphisms of the
  underlying sheaves of modules commuting with the underlying transition morphisms.
* `Stacks.Descent.homForget` and `Stacks.Descent.homLift`: the two directions of the resulting
  bijection on morphisms of canonical descent data.

## Main results

* `Stacks.Descent.descentDataForgetFunctor_obj_toDescentData` and
  `Stacks.Descent.canonicalDescentFunctor_map_eq`: the equivalence carries
  `CategoryTheory.Pseudofunctor.toDescentData` of `qcohPseudofunctor` to
  `AlgebraicGeometry.canonicalDescentFunctor`, on objects and on morphisms.
* `Stacks.Descent.homForget_bijective`: morphisms of the canonical descent data of Stacks 023D
  are exactly morphisms of the canonical descent data for `qcohPseudofunctor`.
* `Stacks.Descent.faithful_canonicalDescentFunctor_of_isPrestack` and
  `Stacks.Descent.nonempty_fullyFaithful_canonicalDescentFunctor_of_isPrestack`: faithfulness and
  full faithfulness in Stacks 023T, from `CategoryTheory.Pseudofunctor.IsPrestack` of
  `qcohPseudofunctor` for the fpqc topology.
* `Stacks.Descent.isEffective_of_isStack`: the effectivity half of Stacks 023T, from
  `CategoryTheory.Pseudofunctor.IsStack` of `qcohPseudofunctor` for the fpqc topology.

## Implementation notes

The two categories of descent data carry the same data, one with the quasi-coherence of each
component packaged into its objects and one with it packaged into the ambient full subcategory,
so the comparison functor is the identity on data.  What is *not* free is the comparison of the
transition morphisms: `CategoryTheory.Pseudofunctor.DescentData` constrains them through
`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom`, which unfolds the pseudofunctor's
`mapComp'`.  Checking that definitional equality inside the instantiated statement of a
structure field costs over a minute, so `Stacks.Descent.hom_pullHom`,
`Stacks.Descent.hom_map_map` and `Stacks.Descent.hom_mapComp'_hom_app` pay it once each, with
the modules kept behind variables, and the fields then match them syntactically.

For the same reason the comparison of the two canonical descent functors is recorded as the
pair of statements `Stacks.Descent.descentDataForgetFunctor_obj_toDescentData` (on objects) and
`Stacks.Descent.canonicalDescentFunctor_map_eq` (on morphisms) rather than as a single equality
or isomorphism of functors: a `CategoryTheory.Functor.ext` over the first of them has to carry
`eqToHom` of it through the second, and that exhausts the heartbeat budget.  For the same reason
there is no equality `qcohPseudofunctor.toDescentData f ⋙ descentDataForgetFunctor =
canonicalDescentFunctor f`, and no `CategoryTheory.Iso` between the two sides either: the two
hom-types involved are definitionally equal, but a statement that leaves their identification to
unification is checked at `instances` transparency and does not terminate within the budget.
Full faithfulness is therefore transferred through `Stacks.Descent.homForget_bijective`, which
mentions only hom-types that are written out.

Reading a morphism of the canonical descent data of Stacks 023D back as one for
`qcohPseudofunctor` needs the transition comparison at a *concrete*
`CategoryTheory.Pseudofunctor.DescentData.ofObj`, where it is no longer behind a variable.  Two
devices make `Stacks.Descent.homLift` elaborate.  First, the compatibility obligation is
discharged by `Stacks.Descent.homMk`, whose two descent data are variables, so the comparison of
the two `comm` fields costs nothing there; what is left at the concrete descent datum is exactly
`Stacks.Descent.hom_toDescentData_obj_hom`, and it is rewritten with its arguments supplied
*explicitly* — with the arguments left as metavariables the rewrite reports that the target is
not type-correct at `implicit` transparency, because the quasi-coherent modules are spelled
`quasicoherentProperty.Obj` in the lemma and `↑(qcohPseudofunctor.obj _)` in the goal.  Second,
the remaining goal is closed by `apply` rather than `exact`: `apply` matches the two sides of the
equation and leaves the two factorisation hypotheses as side goals, whereas `exact` compares the
written-out equations and exhausts the budget.

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 023B](https://stacks.math.columbia.edu/tag/023B)
* [Stacks Project, Tag 023D](https://stacks.math.columbia.edu/tag/023D)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/
@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Bicategory Opposite

universe v u

namespace Stacks.Descent

/-- Quasi-coherence, as a property of objects of the categories of modules through which
`AlgebraicGeometry.modulePullbackPseudofunctor` takes its values. -/
def quasicoherentProperty : modulePullbackPseudofunctor.{u}.ObjectProperty where
  prop X := SheafOfModules.isQuasicoherent X.as.unop.ringCatSheaf

/-- Quasi-coherence is stable under the pullback functors. -/
instance : quasicoherentProperty.{u}.IsClosedUnderMapObj where
  map_obj {_ _ M} hM g := Stacks.Modules.isQuasicoherent_pullback g.as.unop M hM

/-- Quasi-coherence is stable under isomorphisms of modules. -/
instance : quasicoherentProperty.{u}.IsClosedUnderIsomorphisms where
  isClosedUnderIsomorphisms X :=
    inferInstanceAs
      (SheafOfModules.isQuasicoherent X.as.unop.ringCatSheaf).IsClosedUnderIsomorphisms

/-- The pseudofunctor sending a scheme to its category of quasi-coherent modules and a morphism
of schemes to pullback.  This is `AlgebraicGeometry.modulePullbackPseudofunctor` restricted to
the full subcategories of quasi-coherent modules, which is possible by Stacks 01BG. -/
def qcohPseudofunctor : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  quasicoherentProperty.fullsubcategory

section

variable {I : Type v} {S : Scheme.{u}} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ S}

open Pseudofunctor.LocallyDiscreteOpToCat in
/-- Forgetting quasi-coherence commutes with the pullback of a morphism between pullbacks. -/
theorem hom_pullHom {X₁ X₂ : Scheme.{u}} (M₁ : quasicoherentProperty.Obj (.mk (op X₁)))
    (M₂ : quasicoherentProperty.Obj (.mk (op X₂))) {Y : Scheme.{u}} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (qcohPseudofunctor.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (qcohPseudofunctor.map f₂.op.toLoc).toFunctor.obj M₂)
    {Y' : Scheme.{u}} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    (pullHom φ g gf₁ gf₂ hgf₁ hgf₂).hom = pullHom φ.hom g gf₁ gf₂ hgf₁ hgf₂ :=
  rfl

/-- The descent datum for `AlgebraicGeometry.modulePullbackPseudofunctor` underlying a descent
datum for `Stacks.Descent.qcohPseudofunctor`. -/
def descentDataForget (D : qcohPseudofunctor.DescentData f) :
    modulePullbackPseudofunctor.DescentData f where
  obj i := (D.obj i).obj
  hom _ q _ _ f₁ f₂ hf₁ hf₂ := (D.hom q f₁ f₂ hf₁ hf₂).hom
  pullHom_hom _ _ g q q' hq _ _ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ :=
    (hom_pullHom _ _ (D.hom q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ hgf₁ hgf₂).symm.trans
      (congrArg InducedCategory.Hom.hom
        (D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂))
  hom_self _ q _ g hg := congrArg InducedCategory.Hom.hom (D.hom_self q g hg)
  hom_comp _ q _ _ _ f₁ f₂ f₃ hf₁ hf₂ hf₃ :=
    congrArg InducedCategory.Hom.hom (D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃)

/-- The descent datum for `Stacks.Descent.qcohPseudofunctor` carried by a quasi-coherent descent
datum. -/
def descentDataLift (D : QuasicoherentDescentData f) : qcohPseudofunctor.DescentData f where
  obj i := ⟨D.obj.obj i, D.property i⟩
  hom _ q _ _ f₁ f₂ hf₁ hf₂ := ⟨D.obj.hom q f₁ f₂ hf₁ hf₂⟩
  pullHom_hom _ _ g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ :=
    ObjectProperty.hom_ext _
      ((hom_pullHom ⟨D.obj.obj i₁, D.property i₁⟩ ⟨D.obj.obj i₂, D.property i₂⟩
          ⟨D.obj.hom q f₁ f₂ hf₁ hf₂⟩ g gf₁ gf₂ hgf₁ hgf₂).trans
        (D.obj.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂))
  hom_self _ q _ g hg := ObjectProperty.hom_ext _ (D.obj.hom_self q g hg)
  hom_comp _ q _ _ _ f₁ f₂ f₃ hf₁ hf₂ hf₃ :=
    ObjectProperty.hom_ext _ (D.obj.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃)

/-- Forgetting quasi-coherence from the objects of a descent datum, as a functor to the
quasi-coherent descent data of Stacks 023B. -/
@[simps]
def descentDataForgetFunctor :
    qcohPseudofunctor.DescentData f ⥤ QuasicoherentDescentData f where
  obj D := ⟨descentDataForget D, fun i ↦ (D.obj i).property⟩
  map φ := ObjectProperty.homMk
    { hom i := (φ.hom i).hom
      comm _ q _ _ f₁ f₂ hf₁ hf₂ :=
        congrArg InducedCategory.Hom.hom (φ.comm q f₁ f₂ hf₁ hf₂) }

/-- The functor `Stacks.Descent.descentDataForgetFunctor` is faithful. -/
instance : (descentDataForgetFunctor (f := f)).Faithful where
  map_injective {_ _ _ _} h := by
    ext i
    exact ObjectProperty.hom_ext _
      (congrFun (congrArg Pseudofunctor.DescentData.Hom.hom
        (congrArg InducedCategory.Hom.hom h)) i)

/-- The functor `Stacks.Descent.descentDataForgetFunctor` is full. -/
instance : (descentDataForgetFunctor (f := f)).Full where
  map_surjective {_ _} φ :=
    ⟨{ hom i := ⟨φ.hom.hom i⟩
       comm _ q _ _ f₁ f₂ hf₁ hf₂ :=
         ObjectProperty.hom_ext _ (φ.hom.comm q f₁ f₂ hf₁ hf₂) }, rfl⟩

/-- The functor `Stacks.Descent.descentDataForgetFunctor` is essentially surjective. -/
instance : (descentDataForgetFunctor (f := f)).EssSurj where
  mem_essImage D := ⟨descentDataLift D, ⟨Iso.refl _⟩⟩

/-- The functor `Stacks.Descent.descentDataForgetFunctor` is an equivalence of categories. -/
instance : (descentDataForgetFunctor (f := f)).IsEquivalence where

/-- Descent data for `Stacks.Descent.qcohPseudofunctor` are exactly the quasi-coherent descent
data of Stacks 023B: the two categories carry the same data, differing only in whether the
quasi-coherence of the components is packaged into the objects or into the ambient full
subcategory. -/
def descentDataEquivalence :
    qcohPseudofunctor.DescentData f ≌ QuasicoherentDescentData f :=
  descentDataForgetFunctor.asEquivalence

/-- Forgetting quasi-coherence commutes with the pullback functors on morphisms. -/
theorem hom_map_map {b₀ b₁ : LocallyDiscrete Scheme.{u}ᵒᵖ} (g : b₀ ⟶ b₁)
    {M₁ M₂ : quasicoherentProperty.Obj b₀} (φ : M₁ ⟶ M₂) :
    ((qcohPseudofunctor.map g).toFunctor.map φ).hom =
      (modulePullbackPseudofunctor.map g).toFunctor.map φ.hom :=
  rfl

/-- Forgetting quasi-coherence commutes with the composition comparison of the pseudofunctor. -/
theorem hom_mapComp'_hom_app {b₀ b₁ b₂ : LocallyDiscrete Scheme.{u}ᵒᵖ}
    (a : b₀ ⟶ b₁) (b : b₁ ⟶ b₂) (ab : b₀ ⟶ b₂) (h : a ≫ b = ab)
    (M : quasicoherentProperty.Obj b₀) :
    ((qcohPseudofunctor.mapComp' a b ab h).hom.toNatTrans.app M).hom =
      (modulePullbackPseudofunctor.mapComp' a b ab h).hom.toNatTrans.app M.obj :=
  rfl

/-- Inverse form of `Stacks.Descent.hom_mapComp'_hom_app`. -/
theorem hom_mapComp'_inv_app {b₀ b₁ b₂ : LocallyDiscrete Scheme.{u}ᵒᵖ}
    (a : b₀ ⟶ b₁) (b : b₁ ⟶ b₂) (ab : b₀ ⟶ b₂) (h : a ≫ b = ab)
    (M : quasicoherentProperty.Obj b₀) :
    ((qcohPseudofunctor.mapComp' a b ab h).inv.toNatTrans.app M).hom =
      (modulePullbackPseudofunctor.mapComp' a b ab h).inv.toNatTrans.app M.obj :=
  rfl

/-- The transition morphisms of the canonical descent datum of `Stacks.Descent.qcohPseudofunctor`
are, after forgetting quasi-coherence, those of the canonical descent datum of Stacks 023D. -/
theorem hom_toDescentData_obj_hom (M : quasicoherentProperty.Obj (.mk (op S)))
    {Y : Scheme.{u}} (q : Y ⟶ S) {i₁ i₂ : I} (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (((qcohPseudofunctor.toDescentData f).obj M).hom q f₁ f₂ hf₁ hf₂).hom =
      ((canonicalDescentFunctor f).obj M).obj.hom q f₁ f₂ hf₁ hf₂ :=
  rfl

/-- Forgetting quasi-coherence from the canonical descent datum of
`Stacks.Descent.qcohPseudofunctor` gives the canonical descent datum of Stacks 023D. -/
theorem descentDataForgetFunctor_obj_toDescentData
    (M : quasicoherentProperty.Obj (.mk (op S))) :
    descentDataForgetFunctor.obj ((qcohPseudofunctor.toDescentData f).obj M) =
      (canonicalDescentFunctor f).obj M :=
  rfl

/-- `Stacks.Descent.descentDataForgetFunctor` undoes `Stacks.Descent.descentDataLift`. -/
theorem descentDataForgetFunctor_obj_descentDataLift (D : QuasicoherentDescentData f) :
    descentDataForgetFunctor.obj (descentDataLift D) = D :=
  rfl

/-- A morphism of descent data for `Stacks.Descent.qcohPseudofunctor` built from morphisms of the
underlying sheaves of modules commuting with the underlying transition morphisms.

Both the data and the hypothesis are phrased with the two descent data behind variables, which is
what makes the definitional identification of `CategoryTheory.Pseudofunctor.DescentData.Hom.comm`
for the full subcategory with the one for `AlgebraicGeometry.modulePullbackPseudofunctor` free;
see the implementation notes. -/
def homMk {D₁ D₂ : qcohPseudofunctor.DescentData f}
    (b : ∀ i, (D₁.obj i).obj ⟶ (D₂.obj i).obj)
    (hb : ∀ (Y : Scheme.{u}) (q : Y ⟶ S) (i₁ i₂ : I) (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
      (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q),
      (modulePullbackPseudofunctor.map f₁.op.toLoc).toFunctor.map (b i₁) ≫
          (D₂.hom q f₁ f₂ hf₁ hf₂).hom =
        (D₁.hom q f₁ f₂ hf₁ hf₂).hom ≫
          (modulePullbackPseudofunctor.map f₂.op.toLoc).toFunctor.map (b i₂)) :
    D₁ ⟶ D₂ where
  hom i := ⟨b i⟩
  comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := ObjectProperty.hom_ext _ (hb Y q i₁ i₂ f₁ f₂ hf₁ hf₂)

/-- The components of `Stacks.Descent.homMk` are the given morphisms. -/
theorem homMk_hom_hom {D₁ D₂ : qcohPseudofunctor.DescentData f}
    (b : ∀ i, (D₁.obj i).obj ⟶ (D₂.obj i).obj) (hb) (i : I) :
    ((homMk b hb).hom i).hom = b i :=
  rfl

section

variable {M N : quasicoherentProperty.Obj (.mk (op S))}

/-- A morphism of canonical descent data for `Stacks.Descent.qcohPseudofunctor`, read as a
morphism of the canonical descent data of Stacks 023D. -/
def homForget (ψ : (qcohPseudofunctor.toDescentData f).obj M ⟶
    (qcohPseudofunctor.toDescentData f).obj N) :
    (canonicalDescentFunctor f).obj M ⟶ (canonicalDescentFunctor f).obj N :=
  ObjectProperty.homMk
    { hom i := (ψ.hom i).hom
      comm _ q _ _ f₁ f₂ hf₁ hf₂ := by
        rw [← hom_toDescentData_obj_hom, ← hom_toDescentData_obj_hom]
        exact congrArg InducedCategory.Hom.hom (ψ.comm q f₁ f₂ hf₁ hf₂) }

/-- `Stacks.Descent.homForget` is injective: it only repackages the components. -/
theorem homForget_injective : Function.Injective (homForget (f := f) (M := M) (N := N)) :=
  fun _ _ h ↦ Pseudofunctor.DescentData.hom_ext fun i ↦ ObjectProperty.hom_ext _ <|
    congrFun (congrArg Pseudofunctor.DescentData.Hom.hom (congrArg InducedCategory.Hom.hom h)) i

/-- The canonical descent functor of Stacks 023D acts on morphisms as the canonical descent
functor of `Stacks.Descent.qcohPseudofunctor` does. -/
theorem canonicalDescentFunctor_map_eq (φ : M ⟶ N) :
    (canonicalDescentFunctor f).map φ = homForget ((qcohPseudofunctor.toDescentData f).map φ) := by
  apply ObjectProperty.hom_ext
  apply Pseudofunctor.DescentData.hom_ext
  intro i
  rfl

/-- The components of `Stacks.Descent.homForget` are those of the given morphism. -/
theorem homForget_hom_hom (ψ : (qcohPseudofunctor.toDescentData f).obj M ⟶
    (qcohPseudofunctor.toDescentData f).obj N) (i : I) :
    (homForget ψ).hom.hom i = (ψ.hom i).hom :=
  rfl

/-- A morphism of the canonical descent data of Stacks 023D, read as a morphism of the canonical
descent data for `Stacks.Descent.qcohPseudofunctor`.  This is the inverse of
`Stacks.Descent.homForget`; see the implementation notes for the two devices that make it
elaborate. -/
def homLift (ψ : (canonicalDescentFunctor f).obj M ⟶ (canonicalDescentFunctor f).obj N) :
    (qcohPseudofunctor.toDescentData f).obj M ⟶ (qcohPseudofunctor.toDescentData f).obj N :=
  homMk (fun i ↦ ψ.hom.hom i) fun _ q _ _ f₁ f₂ hf₁ hf₂ ↦ by
    rw [hom_toDescentData_obj_hom N q f₁ f₂ hf₁ hf₂,
      hom_toDescentData_obj_hom M q f₁ f₂ hf₁ hf₂]
    apply ψ.hom.comm
    exacts [hf₁, hf₂]

/-- `Stacks.Descent.homForget` undoes `Stacks.Descent.homLift`. -/
theorem homForget_homLift
    (ψ : (canonicalDescentFunctor f).obj M ⟶ (canonicalDescentFunctor f).obj N) :
    homForget (homLift ψ) = ψ :=
  ObjectProperty.hom_ext _ <| Pseudofunctor.DescentData.hom_ext fun i ↦
    (homForget_hom_hom _ i).trans (homMk_hom_hom _ _ i)

/-- `Stacks.Descent.homForget` is surjective: every morphism of the canonical descent data of
Stacks 023D comes from one of the canonical descent data for
`Stacks.Descent.qcohPseudofunctor`. -/
theorem homForget_surjective : Function.Surjective (homForget (f := f) (M := M) (N := N)) :=
  fun ψ ↦ ⟨homLift ψ, homForget_homLift ψ⟩

/-- `Stacks.Descent.homForget` is a bijection on morphisms of canonical descent data. -/
theorem homForget_bijective : Function.Bijective (homForget (f := f) (M := M) (N := N)) :=
  ⟨homForget_injective, homForget_surjective⟩

end

/-- **The faithfulness half of Stacks 023T, reduced to a prestack condition.**  If the
pseudofunctor of quasi-coherent modules is a prestack for the fpqc topology, then for every fpqc
covering family the canonical descent functor on quasi-coherent modules is faithful. -/
theorem faithful_canonicalDescentFunctor_of_isPrestack
    [qcohPseudofunctor.IsPrestack Scheme.fpqcTopology.{u}]
    (hfpqc : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage.{u} S) :
    (canonicalDescentFunctor f).Faithful where
  map_injective {_M _N φ φ'} hφ :=
    (qcohPseudofunctor.fullyFaithfulToDescentData f
      (sieve_ofArrows_mem_fpqcTopology hfpqc)).map_injective
        (homForget_injective ((canonicalDescentFunctor_map_eq φ).symm.trans
          (hφ.trans (canonicalDescentFunctor_map_eq φ'))))

/-- **The full faithfulness half of Stacks 023T, reduced to a prestack condition.**  If the
pseudofunctor of quasi-coherent modules is a prestack for the fpqc topology, then for every fpqc
covering family the canonical descent functor on quasi-coherent modules is fully faithful.

`CategoryTheory.Pseudofunctor.IsStack` extends `CategoryTheory.Pseudofunctor.IsPrestack`, so this
is available from the stack condition alone, as is
`Stacks.Descent.isEffective_of_isStack`. -/
theorem nonempty_fullyFaithful_canonicalDescentFunctor_of_isPrestack
    [qcohPseudofunctor.IsPrestack Scheme.fpqcTopology.{u}]
    (hfpqc : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage.{u} S) :
    Nonempty (canonicalDescentFunctor f).FullyFaithful := by
  have hb := (Functor.FullyFaithful.nonempty_iff_map_bijective
    (qcohPseudofunctor.toDescentData f)).1
      ⟨qcohPseudofunctor.fullyFaithfulToDescentData f
        (sieve_ofArrows_mem_fpqcTopology hfpqc)⟩
  refine (Functor.FullyFaithful.nonempty_iff_map_bijective _).2 fun M N ↦ ?_
  have hcomp : ((canonicalDescentFunctor f).map : (M ⟶ N) → _) =
      homForget ∘ ((qcohPseudofunctor.toDescentData f).map : (M ⟶ N) → _) :=
    funext fun φ ↦ canonicalDescentFunctor_map_eq φ
  rw [hcomp]
  exact homForget_bijective.comp (hb M N)

/-- **The effectivity half of Stacks 023T, reduced to a stack condition.**  If the pseudofunctor
of quasi-coherent modules is a stack for the fpqc topology, then every quasi-coherent descent
datum for an fpqc covering family is effective. -/
theorem isEffective_of_isStack [qcohPseudofunctor.IsStack Scheme.fpqcTopology.{u}]
    (hfpqc : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage.{u} S)
    (D : QuasicoherentDescentData f) : D.IsEffective := by
  have := qcohPseudofunctor.isEquivalence_toDescentData f
    (sieve_ofArrows_mem_fpqcTopology hfpqc)
  obtain ⟨M, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (F := qcohPseudofunctor.toDescentData f) (descentDataLift D)
  exact ⟨M, ⟨eqToIso (descentDataForgetFunctor_obj_toDescentData M).symm ≪≫
    descentDataForgetFunctor.mapIso e ≪≫
      eqToIso (descentDataForgetFunctor_obj_descentDataLift D)⟩⟩
/-- **The converse of `Stacks.Descent.isEffective_of_isStack` at one family.**  If every
quasi-coherent descent datum for a family is effective, then
`CategoryTheory.Pseudofunctor.toDescentData` for `Stacks.Descent.qcohPseudofunctor` is
essentially surjective on that family.

No hypothesis on the family: the two categories of descent data are equivalent by
`Stacks.Descent.descentDataForgetFunctor`, which carries the canonical descent datum of
`qcohPseudofunctor` to the one of Stacks 023D by
`Stacks.Descent.descentDataForgetFunctor_obj_toDescentData`, so an effectivity witness
transports back along it. -/
theorem essSurj_toDescentData_of_forall_isEffective
    (h : ∀ D : QuasicoherentDescentData f, D.IsEffective) :
    (qcohPseudofunctor.toDescentData f).EssSurj where
  mem_essImage D := by
    obtain ⟨M, ⟨e⟩⟩ := h (descentDataForgetFunctor.obj D)
    exact ⟨M, ⟨descentDataForgetFunctor.preimageIso
      (eqToIso (descentDataForgetFunctor_obj_toDescentData M) ≪≫ e)⟩⟩


end

end Stacks.Descent

end

end
