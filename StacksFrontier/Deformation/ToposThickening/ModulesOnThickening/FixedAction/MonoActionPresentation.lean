module

public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.FixedAction.Torsor
public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.FixedAction.ExistenceObstruction
import all StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.FixedAction.Torsor
import all StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.FixedAction.ExistenceObstruction

/-!
# Presentations of the existence obstruction

A `Deformation.ToposThickening.MonoActionPresentation` records an extension over a first order
thickening with injective action map, together with the cokernel sequence of the action map and
the descended extension of `F` by that cokernel. This file attaches to it a universal class in
`Ext²_{i_*O'}(F, I ⊗ F)`, shows the class does not depend on the presentation
(`Deformation.ToposThickening.MonoActionPresentation.universalClass_eq`), and that the
obstruction class is computed by any presentation
(`Deformation.ToposThickening.existenceObstructionClass_eq_obstruction`, **Stacks 08MF**).

The local `implicit_reducible` attributes below are those of the `ExistenceObstruction` section
of `FixedAction/ExistenceObstruction.lean`, where they are explained.

## References

* [Stacks Project, Tag 08MF](https://stacks.math.columbia.edu/tag/08MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u w v' u' w' e

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}}
  {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {i : RingedToposHom X Y}
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify Y.J AddCommGrpCat.{w'}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}]

section ExistenceObstruction

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
  CategoryTheory.ConcreteCategory.hom CategoryTheory.sheafCompose SheafOfModules.forget
  SheafOfModules.restrictScalars PresheafOfModules.restrictScalars ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' PresheafOfModules.restrictScalarsObj

/-! ### Presentations of the obstruction class -/

/-- Restriction of scalars along the structure map of a morphism of ringed topoi. This
abbreviates the functor written out in full above, and keeps the types of the presentations
below readable. -/
noncomputable abbrev structureRestrict (f : RingedToposHom X Y) :=
  SheafOfModules.restrictScalars.{w'}
    (structureRingMap f)

/-- The module `ℐ ⊗_𝒪 F` on which the action map of an extension over the thickening lives. -/
noncomputable abbrev idealTensorModule (hi : FirstOrderThickening i)
    (F : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
        i.toToposHom).obj X.O))) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor
    ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F

/-- A **presentation of the obstruction class** attached to an extension `E` of `F` over the
thickening whose action map `d` is injective: a short exact sequence
`0 ⟶ ℐ ⊗ F ⟶ Q ⟶ C ⟶ 0` continuing `d`, an extension of `F` by `C` over the quotient structure
sheaf, and a comparison map exhibiting the restriction of the latter as the pushout of `E` along
`Q ⟶ C`.

This is the topos analogue of `Deformation.RingedSpaceThickening.ObstructionPresentation`, with
the embedding of the kernel module into an injective module replaced by an extension with
injective action map. The kernel module `Q` and the extension `E` are parameters rather than
fields, because comparing two presentations has to name them. -/
structure MonoActionPresentation (hi : FirstOrderThickening i)
    {F Q : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj Q) 0) where
  /-- The quotient of `Q` by the image of the action map. -/
  C : SheafOfModules.{w'}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))
  /-- The projection of `Q` onto the quotient. -/
  proj : Q ⟶ C
  /-- The action map followed by the projection vanishes. -/
  zero : (extensionActionMap hi E).1 ≫ proj = 0
  /-- `0 ⟶ ℐ ⊗ F ⟶ Q ⟶ C ⟶ 0` is short exact; in particular the action map is injective. -/
  shortExact : (ShortComplex.mk (extensionActionMap hi E).1 proj zero).ShortExact
  /-- An extension of `F` by the quotient over the quotient structure sheaf. -/
  descent : Abelian.YonedaExtension F C 0
  /-- The comparison from the middle term of `E` to the restriction of the middle term of the
  descent. -/
  comparison : E.Z.left ⟶ (structureRestrict i).obj descent.Z.left
  /-- The comparison carries the kernel map of `E` to the projection followed by the kernel map
  of the descent; this is what makes the descent the pushout. -/
  comparison_left : E.f ≫ comparison =
    (structureRestrict i).map proj ≫ (structureRestrict i).map descent.f
  /-- The comparison is compatible with the two surjections onto `F`. -/
  comparison_right : comparison ≫ (structureRestrict i).map descent.g = E.g

variable
  [HasExt.{e} (SheafOfModules.{w'}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))]
  [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  {hi : FirstOrderThickening i}
  {F Q : SheafOfModules.{w'}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}

/-- The **universal obstruction class** of a presentation: the Yoneda product of the class of
the descent with the class of `0 ⟶ ℐ ⊗ F ⟶ Q ⟶ C ⟶ 0`. Every obstruction class of the
presentation is this class pushed forward along a prescribed action map. -/
noncomputable def MonoActionPresentation.universalClass
    {E : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj Q) 0}
    (P : MonoActionPresentation hi E) :
    Abelian.Ext F (idealTensorModule hi F) 2 :=
  (yonedaExtension_shortExact P.descent).extClass.comp P.shortExact.extClass
    (show 1 + 1 = 2 from rfl)

/-- The obstruction class of a presentation at a prescribed action `c` of the square-zero ideal:
the universal class of the presentation pushed forward along `c`. -/
noncomputable def MonoActionPresentation.obstruction
    {E : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj Q) 0}
    (P : MonoActionPresentation hi E)
    (K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    (c : idealTensorModule hi F ⟶ K) : Abelian.Ext F K 2 :=
  P.universalClass.comp (Abelian.Ext.mk₀ c) (add_zero 2)

/-- A map of short exact sequences that is the identity on the cokernels pushes the class of the
source sequence forward to the class of the target sequence. -/
private lemma extClass_comp_mk₀_eq_of_comm {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasExt.{e} 𝒜]
    {A B C A' B' : 𝒜} {f : A ⟶ B} {g : B ⟶ C} {w : f ≫ g = 0} {f' : A' ⟶ B'} {g' : B' ⟶ C}
    {w' : f' ≫ g' = 0} (hS : (ShortComplex.mk f g w).ShortExact)
    (hS' : (ShortComplex.mk f' g' w').ShortExact) (a : A ⟶ A') (b : B ⟶ B')
    (h₁ : f ≫ b = a ≫ f') (h₂ : b ≫ g' = g) :
    hS.extClass.comp (Abelian.Ext.mk₀ a) (add_zero 1) = hS'.extClass := by
  simpa only [Abelian.Ext.mk₀_id_comp] using hS.extClass_naturality hS'
    { τ₁ := a, τ₂ := b, τ₃ := 𝟙 _, comm₁₂ := h₁.symm,
      comm₂₃ := h₂.trans (Category.comp_id _).symm }

omit [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))] in
/-- **The obstruction class of a presentation as a Yoneda product of two extensions.** Pushing
the defining short exact sequence out along the prescribed action `c` gives an extension of the
quotient `C` by `K`; the obstruction class is the Yoneda product of the class of the descent
with the class of that pushout. -/
lemma MonoActionPresentation.obstruction_eq_comp_extClass
    {E : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj Q) 0}
    (P : MonoActionPresentation hi E)
    (K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    (c : idealTensorModule hi F ⟶ K) (Pp : Abelian.YonedaExtension P.C K 0)
    (uP : Q ⟶ Pp.Z.left) (hPu : (extensionActionMap hi E).1 ≫ uP = c ≫ Pp.f)
    (hPg : uP ≫ Pp.g = P.proj) :
    P.obstruction K c =
      (yonedaExtension_shortExact P.descent).extClass.comp
        (yonedaExtension_shortExact Pp).extClass (show 1 + 1 = 2 from rfl) := by
  have hext : P.shortExact.extClass.comp (Abelian.Ext.mk₀ c) (add_zero 1) =
      (yonedaExtension_shortExact Pp).extClass := by
    exact extClass_comp_mk₀_eq_of_comm P.shortExact (yonedaExtension_shortExact Pp) c uP
      hPu hPg
  rw [← hext]
  exact Abelian.Ext.comp_assoc_of_third_deg_zero _ _ _ _

/-- **The descent of a presentation is determined by the extension and the projection.** Its
`Ext` class restricts to the class of `E` pushed forward along `Q ⟶ C`; since restriction of
scalars is injective on `Ext¹`, this pins down the class of the descent. -/
lemma mapExtAddHom_descent_extClass
    {C : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    {E : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj Q) 0}
    (proj : Q ⟶ C) (D : Abelian.YonedaExtension F C 0)
    (cmp : E.Z.left ⟶ (structureRestrict i).obj D.Z.left)
    (hcmp₁ : E.f ≫ cmp = (structureRestrict i).map proj ≫ (structureRestrict i).map D.f)
    (hcmp₂ : cmp ≫ (structureRestrict i).map D.g = E.g) :
    (structureRestrict i).mapExtAddHom F C 1 (yonedaExtension_shortExact D).extClass =
      (extensionClass F Q E).comp
        (Abelian.Ext.mk₀ ((structureRestrict i).map proj)) (add_zero 1) := by
  have hex := restrictScalars_exact
    (structureRingMap i)
  have hlim : PreservesFiniteLimits (structureRestrict i) := hex.1
  have hcolim : PreservesFiniteColimits (structureRestrict i) := hex.2
  rw [Functor.mapExtAddHom_apply, Abelian.Ext.mapExactFunctor_extClass]
  exact (extClass_comp_mk₀_eq_of_comm (yonedaExtension_shortExact E)
    ((yonedaExtension_shortExact D).map_of_exact (structureRestrict i)) _ cmp hcmp₁ hcmp₂).symm

/-- Composing two maps of extensions: if `u` maps an extension with kernel map `f` to one with
kernel map `f'` over `a`, and `v` maps the latter to one with kernel map `f''`, the composite does
the same over `a` for `f''`. -/
private lemma comp_extension_hom_compat {𝒞 : Type*} [Category 𝒞] {K K' Z Z' Z'' B : 𝒞}
    {f : K ⟶ Z} {f' : K' ⟶ Z'} {f'' : K' ⟶ Z''} {g : Z ⟶ B} {g' : Z' ⟶ B} {g'' : Z'' ⟶ B}
    {a : K ⟶ K'} {u : Z ⟶ Z'} {v : Z' ⟶ Z''} (hu : f ≫ u = a ≫ f') (hg : u ≫ g' = g)
    (hv : f' ≫ v = f'') (hg' : v ≫ g'' = g') : f ≫ u ≫ v = a ≫ f'' ∧ (u ≫ v) ≫ g'' = g := by
  exact ⟨by rw [← hv, ← Category.assoc, hu, Category.assoc],
    by rw [Category.assoc, hg', hg]⟩

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [HasExt.{e} (SheafOfModules.{w'}
  (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))] in
/-- **An extension receiving a prescribed class receives a map of extensions.** If the class of
`E` pushed forward along a map `γ` of kernel modules is the class of `E'`, then there is a map of
middle terms over `F` inducing `γ` on the kernel modules. This is the converse of
`extensionClass_pushout`. -/
private lemma exists_hom_of_extensionClass_comp_eq
    {L : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj Q) 0)
    (E' : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj L) 0) (γ : Q ⟶ L)
    (h : (extensionClass F Q E).comp
      (Abelian.Ext.mk₀ ((structureRestrict i).map γ)) (add_zero 1) = extensionClass F L E') :
    ∃ u : E.Z.left ⟶ E'.Z.left,
      E.f ≫ u = (structureRestrict i).map γ ≫ E'.f ∧ u ≫ E'.g = E.g := by
  obtain ⟨E'', u, hu, hg⟩ := Abelian.shortExact_pushout (yonedaExtension_shortExact E)
    ((structureRestrict i).map γ)
  have hcl : extensionClass F L E'' = extensionClass F L E' :=
    (extensionClass_pushout E E'' γ u hu hg).symm.trans h
  obtain ⟨φ, hφ₁, hφ₂⟩ := ((Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum
    (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    ((structureRestrict i).obj F) ((structureRestrict i).obj L)).2.1 _ _ _ _ _ _ _ _
    (yonedaExtension_shortExact E'') (yonedaExtension_shortExact E')).1 hcl
  exact ⟨u ≫ φ.hom, comp_extension_hom_compat hu hg hφ₁ hφ₂⟩

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [HasExt.{e} (SheafOfModules.{w'}
  (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))] in
/-- **A common refinement of two extensions of the same module.** Realize the sum of the two
classes pushed into the biproduct of the two kernel modules by an extension; it maps to both
extensions, because each projection of the biproduct kills the other summand. -/
private lemma exists_extension_hom_pair
    {Q₂ : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E₁ : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj Q) 0)
    (E₂ : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj Q₂) 0) :
    ∃ (E₃ : Abelian.YonedaExtension ((structureRestrict i).obj F)
        ((structureRestrict i).obj (Q ⊞ Q₂)) 0)
      (u₁ : E₃.Z.left ⟶ E₁.Z.left) (u₂ : E₃.Z.left ⟶ E₂.Z.left),
      (E₃.f ≫ u₁ = (structureRestrict i).map biprod.fst ≫ E₁.f ∧ u₁ ≫ E₁.g = E₃.g) ∧
        E₃.f ≫ u₂ = (structureRestrict i).map biprod.snd ≫ E₂.f ∧ u₂ ≫ E₂.g = E₃.g := by
  obtain ⟨E₃, hE₃⟩ := exists_extensionClass_eq.{_, _, _, _, _, _, e} F (Q ⊞ Q₂)
    ((extensionClass F Q E₁).comp
        (Abelian.Ext.mk₀ ((structureRestrict i).map biprod.inl)) (add_zero 1) +
      (extensionClass F Q₂ E₂).comp
        (Abelian.Ext.mk₀ ((structureRestrict i).map biprod.inr)) (add_zero 1))
  obtain ⟨u₁, hu₁, hg₁⟩ := exists_hom_of_extensionClass_comp_eq E₃ E₁ biprod.fst (by
    rw [hE₃]
    simp only [Abelian.Ext.add_comp, Abelian.Ext.comp_assoc_of_second_deg_zero,
      Abelian.Ext.mk₀_comp_mk₀, ← CategoryTheory.Functor.map_comp, biprod.inl_fst,
      biprod.inr_fst, CategoryTheory.Functor.map_zero, Abelian.Ext.mk₀_zero,
      Abelian.Ext.comp_zero, add_zero]
    rw [CategoryTheory.Functor.map_id, Abelian.Ext.comp_mk₀_id])
  obtain ⟨u₂, hu₂, hg₂⟩ := exists_hom_of_extensionClass_comp_eq E₃ E₂ biprod.snd (by
    rw [hE₃]
    simp only [Abelian.Ext.add_comp, Abelian.Ext.comp_assoc_of_second_deg_zero,
      Abelian.Ext.mk₀_comp_mk₀, ← CategoryTheory.Functor.map_comp, biprod.inl_snd,
      biprod.inr_snd, CategoryTheory.Functor.map_zero, Abelian.Ext.mk₀_zero,
      Abelian.Ext.comp_zero, zero_add]
    rw [CategoryTheory.Functor.map_id, Abelian.Ext.comp_mk₀_id])
  exact ⟨E₃, u₁, u₂, ⟨hu₁, hg₁⟩, hu₂, hg₂⟩

omit [HasExt.{e} (SheafOfModules.{w'}
  (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))]
  [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))] in
/-- A presentation of the obstruction class, assembled from a short exact sequence continuing a
map that is *equal* to the action map of `E`. Passing the action map as an equation keeps the
short exact sequence out of the dependent position its proof of vanishing would otherwise sit
in. -/
noncomputable def MonoActionPresentation.ofShortExact (hi : FirstOrderThickening i)
    (E : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj Q) 0)
    {C : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    {d : idealTensorModule hi F ⟶ Q} (hd : (extensionActionMap hi E).1 = d) (proj : Q ⟶ C)
    (w : d ≫ proj = 0) (hSE : (ShortComplex.mk d proj w).ShortExact)
    (descent : Abelian.YonedaExtension F C 0)
    (cmp : E.Z.left ⟶ (structureRestrict i).obj descent.Z.left)
    (hcmp₁ : E.f ≫ cmp =
      (structureRestrict i).map proj ≫ (structureRestrict i).map descent.f)
    (hcmp₂ : cmp ≫ (structureRestrict i).map descent.g = E.g) :
    MonoActionPresentation hi E := by
  subst hd
  exact { C := C, proj := proj, zero := w, shortExact := hSE, descent := descent
          comparison := cmp, comparison_left := hcmp₁, comparison_right := hcmp₂ }

omit [HasExt.{e} (SheafOfModules.{w'}
  (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))]
  [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))] in
/-- The sequence `0 ⟶ ℐ ⊗ F ⟶ Q ⟶ coker d ⟶ 0` cut out by an injective action map `d` is short
exact. -/
private lemma shortExact_cokernel_actionMap (hi : FirstOrderThickening i)
    (E : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj Q) 0)
    (hdm : Mono (extensionActionMap hi E).1) :
    (ShortComplex.mk (extensionActionMap hi E).1
      (cokernel.π (extensionActionMap hi E).1)
      (cokernel.condition (extensionActionMap hi E).1)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) hdm inferInstance

omit [HasExt.{e} (SheafOfModules.{w'}
  (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))]
  [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))] in
/-- **The descent attached to an extension with injective action map.** Push the extension out
along the cokernel of its action map; the pushout has vanishing action map, hence is restricted
from an extension over the quotient structure sheaf, and the pushout map composed with that
identification is the comparison a presentation asks for. -/
private lemma exists_descent_of_mono_action (hi : FirstOrderThickening i)
    (E : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj Q) 0) :
    ∃ (D : Abelian.YonedaExtension F (cokernel (extensionActionMap hi E).1) 0)
      (cmp : E.Z.left ⟶ (structureRestrict i).obj D.Z.left),
      E.f ≫ cmp =
          (structureRestrict i).map (cokernel.π (extensionActionMap hi E).1) ≫
            (structureRestrict i).map D.f ∧
        cmp ≫ (structureRestrict i).map D.g = E.g := by
  obtain ⟨D', uD, hDu, hDg⟩ := Abelian.shortExact_pushout (yonedaExtension_shortExact E)
    ((structureRestrict i).map (cokernel.π (extensionActionMap hi E).1))
  have hD' : (extensionActionMap hi D').1 = 0 :=
    (extensionActionMap_naturality hi E D' (cokernel.π (extensionActionMap hi E).1)
      uD hDu hDg).symm.trans (cokernel.condition _)
  obtain ⟨D, mD, hmD₁, hmD₂⟩ := zeroAction_extension_descend hi D' hD'
  exact ⟨D, uD ≫ mD.inv, comp_extension_hom_compat hDu hDg ((Iso.comp_inv_eq _).2 hmD₁.symm)
    ((Iso.inv_comp_eq _).2 hmD₂.symm)⟩

omit [HasExt.{e} (SheafOfModules.{w'}
  (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))]
  [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))] in
/-- **Every extension with injective action map carries a presentation.** Take the cokernel of
the action map and the descent of the pushout of the extension along it. -/
lemma exists_monoActionPresentation (hi : FirstOrderThickening i)
    (E : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj Q) 0)
    (hdm : Mono (extensionActionMap hi E).1) :
    Nonempty (MonoActionPresentation hi E) := by
  obtain ⟨D, cmp, hcmp₁, hcmp₂⟩ := exists_descent_of_mono_action hi E
  exact ⟨{ C := cokernel (extensionActionMap hi E).1
           proj := cokernel.π (extensionActionMap hi E).1
           zero := cokernel.condition _
           shortExact := shortExact_cokernel_actionMap hi E hdm
           descent := D
           comparison := cmp
           comparison_left := hcmp₁
           comparison_right := hcmp₂ }⟩

omit [HasExt.{e} (SheafOfModules.{w'}
  (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))]
  [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))] in
/-- **Every module over the quotient structure sheaf carries a presentation of the obstruction
class.** It carries an extension with injective action map, and such an extension carries a
presentation. -/
lemma exists_extension_monoActionPresentation (hi : FirstOrderThickening i)
    (F : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
        i.toToposHom).obj X.O))) :
    ∃ (Q : SheafOfModules.{w'}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
          i.toToposHom).obj X.O)))
      (E : Abelian.YonedaExtension ((structureRestrict i).obj F)
        ((structureRestrict i).obj Q) 0),
      Nonempty (MonoActionPresentation hi E) := by
  obtain ⟨Q, E, hdm⟩ := exists_extension_with_mono_action hi F
  exact ⟨Q, E, exists_monoActionPresentation hi E hdm⟩

/-- **A map of extensions identifies the universal obstruction classes.** If the middle term of
`E₂` maps to the middle term of `E₁` over `F`, inducing `γ` on the kernel modules, then any
presentation of `E₁` and any presentation of `E₂` have the same universal class: the map of
quotients induced by `γ` identifies the two defining short exact sequences, and the two descent
classes correspond because restriction of scalars is injective on `Ext¹`. -/
theorem MonoActionPresentation.universalClass_eq_of_hom
    {Q₂ : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    {E₁ : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj Q) 0}
    {E₂ : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj Q₂) 0}
    (P₁ : MonoActionPresentation hi E₁) (P₂ : MonoActionPresentation hi E₂)
    (γ : Q₂ ⟶ Q) (u : E₂.Z.left ⟶ E₁.Z.left)
    (hu : E₂.f ≫ u = (structureRestrict i).map γ ≫ E₁.f) (hg : u ≫ E₁.g = E₂.g) :
    P₁.universalClass = P₂.universalClass := by
  have hff := hi.restrictScalarsFullyFaithful
  have hfull : (structureRestrict i).Full := hff.full
  have hfaith : (structureRestrict i).Faithful := hff.faithful
  have hd : (extensionActionMap hi E₂).1 ≫ γ = (extensionActionMap hi E₁).1 :=
    extensionActionMap_naturality hi E₂ E₁ γ u hu hg
  have hepi : Epi P₂.proj := P₂.shortExact.epi_g
  have hzero : (extensionActionMap hi E₂).1 ≫ γ ≫ P₁.proj = 0 :=
    (Category.assoc _ _ _).symm.trans ((congrArg (fun z => z ≫ P₁.proj) hd).trans P₁.zero)
  obtain ⟨cbar, hbar⟩ := P₂.shortExact.exact.desc' (γ ≫ P₁.proj) hzero
  have hξ : (yonedaExtension_shortExact P₁.descent).extClass =
      (yonedaExtension_shortExact P₂.descent).extClass.comp
        (Abelian.Ext.mk₀ cbar) (add_zero 1) := by
    apply (structureRestrict i).extMap_injective_of_fullyFaithful F P₁.C
    rw [Functor.mapExtAddHom_comp_mk₀,
      mapExtAddHom_descent_extClass P₁.proj P₁.descent P₁.comparison
        P₁.comparison_left P₁.comparison_right,
      mapExtAddHom_descent_extClass P₂.proj P₂.descent P₂.comparison
        P₂.comparison_left P₂.comparison_right,
      Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
      ← CategoryTheory.Functor.map_comp, hbar, CategoryTheory.Functor.map_comp,
      ← Abelian.Ext.mk₀_comp_mk₀, ← Abelian.Ext.comp_assoc_of_second_deg_zero,
      extensionClass_pushout E₂ E₁ γ u hu hg]
  have hnat := Abelian.comp_extClass_naturality P₁.shortExact P₂.shortExact
    (⟨𝟙 _, γ, cbar, (Category.id_comp _).trans hd.symm, hbar.symm⟩ :
      ShortComplex.mk (extensionActionMap hi E₂).1 P₂.proj P₂.zero ⟶
        ShortComplex.mk (extensionActionMap hi E₁).1 P₁.proj P₁.zero)
    (yonedaExtension_shortExact P₁.descent).extClass
    (yonedaExtension_shortExact P₂.descent).extClass hξ
  exact hnat.trans (Abelian.Ext.comp_mk₀_id _)

/-- **The universal obstruction class does not depend on the presentation.** Two presentations
are compared through a common refinement of their two extensions. -/
theorem MonoActionPresentation.universalClass_eq
    {Q₂ : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    {E₁ : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj Q) 0}
    {E₂ : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj Q₂) 0}
    (P₁ : MonoActionPresentation hi E₁) (P₂ : MonoActionPresentation hi E₂) :
    P₁.universalClass = P₂.universalClass := by
  obtain ⟨E₃, u₁, u₂, ⟨hu₁, hg₁⟩, hu₂, hg₂⟩ := exists_extension_hom_pair E₁ E₂
  have hm₁ : Mono (extensionActionMap hi E₁).1 := P₁.shortExact.mono_f
  have hd₁ : (extensionActionMap hi E₃).1 ≫ biprod.fst = (extensionActionMap hi E₁).1 :=
    extensionActionMap_naturality hi E₃ E₁ biprod.fst u₁ hu₁ hg₁
  obtain ⟨P₃⟩ := exists_monoActionPresentation hi E₃ (mono_of_mono_fac hd₁)
  exact (MonoActionPresentation.universalClass_eq_of_hom P₁ P₃ biprod.fst u₁ hu₁ hg₁).trans
    (MonoActionPresentation.universalClass_eq_of_hom P₂ P₃ biprod.snd u₂ hu₂ hg₂).symm

/-- The value of `obstructionFromMonoAction`, read off its construction: the Yoneda product of
the class of the descent of the pushout of `E` along the cokernel of its action map with the
class of the pushout of that cokernel sequence along `c`. -/
private lemma obstructionFromMonoAction_val (hi : FirstOrderThickening i)
    (F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    (c : idealTensorModule hi F ⟶ K)
    {Q : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj Q) 0)
    (hdm : Mono (extensionActionMap hi E).1)
    (hS : (ShortComplex.mk (extensionActionMap hi E).1
      (cokernel.π (extensionActionMap hi E).1)
      (cokernel.condition (extensionActionMap hi E).1)).ShortExact)
    (hpushD : ∃ (D' : Abelian.YonedaExtension ((structureRestrict i).obj F)
          ((structureRestrict i).obj (cokernel (extensionActionMap hi E).1)) 0)
        (u : E.Z.left ⟶ D'.Z.left),
        E.f ≫ u =
            (structureRestrict i).map (cokernel.π (extensionActionMap hi E).1) ≫ D'.f ∧
          u ≫ D'.g = E.g)
    (hD' : (extensionActionMap hi (Classical.choose hpushD)).1 = 0) :
    (obstructionFromMonoAction hi F K c E hdm).1 =
      (yonedaExtension_shortExact (Classical.choose
          (zeroAction_extension_descend hi (Classical.choose hpushD) hD'))).extClass.comp
        (yonedaExtension_shortExact
          (Classical.choose (Abelian.shortExact_pushout hS c))).extClass
        (show 1 + 1 = 2 from rfl) :=
  rfl

/-- The obstruction class produced from an extension with injective action map is the
obstruction class of a presentation built on that extension, the one whose quotient is the
cokernel of the action map. -/
private lemma obstructionFromMonoAction_eq_obstruction (hi : FirstOrderThickening i)
    (F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    (c : idealTensorModule hi F ⟶ K)
    {Q : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj Q) 0)
    (hdm : Mono (extensionActionMap hi E).1) :
    ∃ P : MonoActionPresentation hi E,
      (obstructionFromMonoAction hi F K c E hdm).1 = P.obstruction K c := by
  classical
  have hS := shortExact_cokernel_actionMap hi E hdm
  have hpushD := Abelian.shortExact_pushout (yonedaExtension_shortExact E)
    ((structureRestrict i).map (cokernel.π (extensionActionMap hi E).1))
  have hDu : E.f ≫ Classical.choose (Classical.choose_spec hpushD) =
      (structureRestrict i).map (cokernel.π (extensionActionMap hi E).1) ≫
        (Classical.choose hpushD).f :=
    (Classical.choose_spec (Classical.choose_spec hpushD)).1
  have hDg : Classical.choose (Classical.choose_spec hpushD) ≫ (Classical.choose hpushD).g =
      E.g := (Classical.choose_spec (Classical.choose_spec hpushD)).2
  have hD' : (extensionActionMap hi (Classical.choose hpushD)).1 = 0 :=
    (extensionActionMap_naturality hi E (Classical.choose hpushD)
      (cokernel.π (extensionActionMap hi E).1)
      (Classical.choose (Classical.choose_spec hpushD)) hDu hDg).symm.trans
      (cokernel.condition _)
  have hdesc := zeroAction_extension_descend hi (Classical.choose hpushD) hD'
  have hmD₁ : (structureRestrict i).map (Classical.choose hdesc).f ≫
      (Classical.choose (Classical.choose_spec hdesc)).hom = (Classical.choose hpushD).f :=
    (Classical.choose_spec (Classical.choose_spec hdesc)).1
  have hmD₂ : (Classical.choose (Classical.choose_spec hdesc)).hom ≫
      (Classical.choose hpushD).g =
      (structureRestrict i).map (Classical.choose hdesc).g :=
    (Classical.choose_spec (Classical.choose_spec hdesc)).2
  have hcomp := comp_extension_hom_compat hDu hDg ((Iso.comp_inv_eq _).2 hmD₁.symm)
    ((Iso.inv_comp_eq _).2 hmD₂.symm)
  have hPu : (extensionActionMap hi E).1 ≫
      Classical.choose (Classical.choose_spec (Abelian.shortExact_pushout hS c)) =
      c ≫ (Classical.choose (Abelian.shortExact_pushout hS c)).f :=
    (Classical.choose_spec (Classical.choose_spec (Abelian.shortExact_pushout hS c))).1
  have hPg : Classical.choose (Classical.choose_spec (Abelian.shortExact_pushout hS c)) ≫
      (Classical.choose (Abelian.shortExact_pushout hS c)).g =
      cokernel.π (extensionActionMap hi E).1 :=
    (Classical.choose_spec (Classical.choose_spec (Abelian.shortExact_pushout hS c))).2
  let P : MonoActionPresentation hi E :=
    { C := cokernel (extensionActionMap hi E).1
      proj := cokernel.π (extensionActionMap hi E).1
      zero := cokernel.condition _
      shortExact := hS
      descent := Classical.choose hdesc
      comparison := Classical.choose (Classical.choose_spec hpushD) ≫
        (Classical.choose (Classical.choose_spec hdesc)).inv
      comparison_left := hcomp.1
      comparison_right := hcomp.2 }
  exact ⟨P, (obstructionFromMonoAction_val hi F K c E hdm hS hpushD hD').trans
    (MonoActionPresentation.obstruction_eq_comp_extClass P K c
      (Classical.choose (Abelian.shortExact_pushout hS c))
      (Classical.choose (Classical.choose_spec (Abelian.shortExact_pushout hS c)))
      hPu hPg).symm⟩

/-- **Stacks 08MF.** The obstruction class is computed by any presentation: it is the Yoneda
product of the class of the descent with the class of the sequence defining the action map,
pushed forward along the prescribed action.

This is the handle on the obstruction class that `existenceObstructionClass_eq_zero_iff` cannot
give: an identity between classes rather than a vanishing criterion, which is what lets two
obstruction classes be compared. -/
theorem existenceObstructionClass_eq_obstruction (hi : FirstOrderThickening i)
    (F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
    (c : idealTensorModule hi F ⟶ K)
    {Q : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    {E : Abelian.YonedaExtension ((structureRestrict i).obj F)
      ((structureRestrict i).obj Q) 0}
    (P : MonoActionPresentation hi E) :
    existenceObstructionClass hi F K c = P.obstruction K c := by
  classical
  obtain ⟨P₀, h₀⟩ := obstructionFromMonoAction_eq_obstruction hi F K c
    (Classical.choose (Classical.choose_spec (exists_extension_with_mono_action hi F)))
    (Classical.choose_spec (Classical.choose_spec (exists_extension_with_mono_action hi F)))
  refine Eq.trans h₀ ?_
  exact congrArg (fun z => z.comp (Abelian.Ext.mk₀ c) (add_zero 2))
    (MonoActionPresentation.universalClass_eq P₀ P)

end ExistenceObstruction

end Deformation.ToposThickening

end
