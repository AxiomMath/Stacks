module

public import StacksFrontier.AlgebraicGeometry.ExternalTensorPullback.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso

/-!
# Sections of the pullback-tensor comparison

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `A`, `B` be sheaves of
`𝒪_Y`-modules. The canonical comparison of [Stacks, Tag 01CD],
`f^*(A ⊗_{𝒪_Y} B) ⟶ f^*A ⊗_{𝒪_X} f^*B`, carries the image of a pure tensor `x ⊗ y` of local
sections of `A` and `B` to the tensor of the images of `x` and of `y`; that is
`Stacks.RingedSpace.comparison_pullbackUnit_unit_tmul`.

This file reads the same computation at the scheme level, for
`AlgebraicGeometry.Scheme.Modules.pullback` and
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`.

## Main definitions

* `Stacks.Tag01VSPullbackTensor.modulesPullbackUnit`: a local section of a sheaf of modules `F`
  on `Y`, carried to a local section of `g^*F` over the preimage open by the unit of the
  adjunction `g^* ⊣ g_*` of schemes.
* `Stacks.Tag01VSPullbackTensor.modulesPullbackUnitTop`: the same, for a section over an open
  whose preimage is the whole of the source, read as a global section of `g^*F`.
* `Stacks.Tag01VSPullbackTensor.externalTensorSection`: the section of `F ⊠ G` over an open of
  `P ×_S Q` inside `pr₁⁻¹U ∩ pr₂⁻¹V` attached to a section of `F` over `U` and a section of `G`
  over `V`. No chart enters its definition.

## Main results

* `Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso_hom_modulesPullbackUnit`: the same
  computation for [Stacks, Tag 01CD] at the scheme level.
* `Stacks.Tag01VSPullbackTensor.tensorSheafMapIso_hom_toTensorSheafSection`: functoriality of the
  tensor product sheaf on a pure tensor of sections.
* `Stacks.Tag01VSPullbackTensor.modulesPullbackUnit_pullbackComp_inv` and
  `modulesPullbackUnit_pullbackComp_hom`: the unit is compatible with pseudofunctoriality of the
  pullback, so that the unit of a composite is the composite of the units.
* `Stacks.Tag01VSPullbackTensor.modulesHomApp_trans`: the action on sections of a composite of two
  isomorphisms of sheaves of modules.
* `Stacks.Tag01VSPullbackTensor.modulesPullbackUnit_pullbackCongr_hom` and
  `modulesPullbackUnit_pullbackCongr_inv`: the identification of the pullbacks along two equal
  morphisms carries the unit image of a section along one to the unit image along the other,
  restricted along the induced equality of preimage opens. The companions
  `modulesPullbackUnit_pullbackCongr_hom_top` and `modulesPullbackUnit_pullbackCongr_inv_top` are
  the same statements over the whole space, where the two preimage opens are both `⊤` and no
  restriction appears.
* `Stacks.Tag01VSPullbackTensor.modulesPullbackUnit_pullbackCompCongrIso_hom_top` and
  `modulesPullbackUnit_pullbackCompCongrIso_inv_top`: the two previous families combined, so that
  the identification `g ^* (h ^* M) ≅ k ^* M` attached to an equation `g ≫ h = k` matches the
  unit image of a global section along `k` with its unit image along `h` and then `g`.
* `Stacks.Tag01VSPullbackTensor.pullbackLift_externalTensorProductIso_hom_modulesPullbackUnit`:
  the identification of the pullback of an external tensor product along a pair with the tensor
  product of the two pullbacks, on global sections, carries the pure tensor built from `x` and `y`
  to the pure tensor of their unit images along `j` and `j'`.
* `Stacks.Tag01VSPullbackTensor.homApp_presheaf_map` and `modulesPullbackUnit_map`: a morphism of
  sheaves of modules, and in particular the unit of the pullback, commutes with restriction of
  sections.
* `Stacks.Tag01VSPullbackTensor.toTensorSheafSection_presheaf_map`: the canonical map into the
  sheaf tensor product commutes with restriction, on a pure tensor.
* `Stacks.Tag01VSPullbackTensor.modulesPullbackUnit_pullbackCompCongrIso_hom` and
  `modulesPullbackUnit_pullbackCompCongrIso_inv`: the general-open forms of the two `_top`
  statements above, where the two preimage opens are equal only propositionally and an `eqToHom`
  transport appears.
* `Stacks.Tag01VSPullbackTensor.pullbackLift_externalTensorProductIso_hom_externalTensorSection`:
  the general-open form of the previous statement, for sections of `F` over `U` and of `G` over
  `V` rather than global ones.

## Implementation notes

No `@[stacks]` attribute. Tag 01CD is carried elsewhere, on
`Stacks.RingedSpace.comparisonBifunctorIso` and `Stacks.PullbackTensorIso.pullbackTensorIso`;
what is here is the section-level computation of the morphism those statements are about.

The scheme-level statements are the ringed-space ones at `g.toLRSHom.toShHom`, which is the
comparison `Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso` is built from.

The compatibility of the unit with `AlgebraicGeometry.Scheme.Modules.pullbackComp` comes from
`AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv` — the conjugate of the inverse
of the pseudofunctor constraint is the pushforward constraint, whose action on sections is the
identity — through `CategoryTheory.unit_conjugateEquiv`.

`AlgebraicGeometry.Scheme.Modules.pullbackCongr` is an `eqToIso`, so its action on sections is a
transport and not the identity: a section of `f ^* M` lives over `f ⁻¹ U` and a section of `g ^* M`
over `g ⁻¹ U`, and those two opens are equal only propositionally. Over the whole space both are
`⊤` definitionally, which is why the `_top` forms carry no restriction; and `⊤` is the only open at
which `AlgebraicGeometry.moduleSpecΓFunctor` is evaluated.

Away from `⊤` the transports do not disappear, and the general-open statements are phrased with
them in place. Two sections of `F ⊠ G` attached to a section of `F` over `U` and a section of `G`
over `V` cannot live over one of `pr₁⁻¹U` or `pr₂⁻¹V`, so
`Stacks.Tag01VSPullbackTensor.externalTensorSection` takes a third open inside both and restricts
there; `Stacks.Tag01VSPullbackTensor.presheaf_map_map` collapses the resulting chains of
restrictions, the opens of a scheme being a poset in which a composite is the only morphism
there is.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped TensorProduct

universe u

namespace Stacks.Tag01VSPullbackTensor

open Stacks.SheafOfModules.TensorStalkRingedSpace

/-- A local section of a sheaf of `𝒪_Y`-modules `F` over `U`, carried to a local section of the
pullback `g^*F` over `g⁻¹U` by the unit of the adjunction `g^* ⊣ g_*`. -/
def modulesPullbackUnit {X Y : Scheme.{u}} (g : X ⟶ Y) (F : Y.Modules) (U : Y.Opens)
    (s : Γ(F, U)) : Γ((Scheme.Modules.pullback g).obj F, g ⁻¹ᵁ U) :=
  Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F) U s

/-- **[Stacks, Tag 01CD] on sections, at the scheme level.** The identification
`g^*(A ⊗_{𝒪_Y} B) ≅ g^*A ⊗_{𝒪_X} g^*B` carries the pullback of the section of `A ⊗ B` coming
from a pure tensor `x ⊗ y` to the section coming from the pure tensor of the pullbacks of `x`
and of `y`. -/
theorem schemePullbackTensorIso_hom_modulesPullbackUnit {X Y : Scheme.{u}} (g : X ⟶ Y)
    (A B : Y.Modules) (U : Y.Opens) (x : Γ(A, U)) (y : Γ(B, U)) :
    Scheme.Modules.Hom.app (schemePullbackTensorIso g A B).hom (g ⁻¹ᵁ U)
        (modulesPullbackUnit g
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(Y.toRingedSpace).presheaf, (Y.toRingedSpace).IsSheaf⟩).obj (A)).obj (B))) U
          (toTensorSheafSection Y.toRingedSpace A B (Opposite.op U) (x ⊗ₜ y)))
      = toTensorSheafSection X.toRingedSpace ((Scheme.Modules.pullback g).obj A)
          ((Scheme.Modules.pullback g).obj B) (Opposite.op (g ⁻¹ᵁ U))
          (modulesPullbackUnit g A U x ⊗ₜ modulesPullbackUnit g B U y) :=
  Stacks.RingedSpace.comparison_pullbackUnit_unit_tmul g.toLRSHom.toShHom A B
    (Opposite.op U) x y

/-- Functoriality of the tensor product sheaf on a pure tensor of sections: the morphism induced
by `eA` and `eB` carries the section coming from `x ⊗ y` to the one coming from
`eA x ⊗ eB y`. -/
theorem tensorSheafMapIso_hom_toTensorSheafSection {X : Scheme.{u}} {A A' B B' : X.Modules}
    (eA : A ≅ A') (eB : B ≅ B') (U : X.Opens) (x : Γ(A, U)) (y : Γ(B, U)) :
    Scheme.Modules.Hom.app (tensorSheafMapIso eA eB).hom U
        (toTensorSheafSection X.toRingedSpace A B (Opposite.op U) (x ⊗ₜ y))
      = toTensorSheafSection X.toRingedSpace A' B' (Opposite.op U)
          (Scheme.Modules.Hom.app eA.hom U x ⊗ₜ Scheme.Modules.Hom.app eB.hom U y) :=
  Stacks.RingedSpace.tensorSheaf_map_unit_tmul X.toRingedSpace eA.hom eB.hom (Opposite.op U) x y

/-- The unit of the module pullback is compatible with pseudofunctoriality: the inverse of the
constraint `g^*(h^*M) ≅ (g ≫ h)^*M` carries the pullback of a section along `g ≫ h` to its
pullback along `h` and then along `g`. -/
theorem modulesPullbackUnit_pullbackComp_inv {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (s : Γ(M, U)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp g h).inv.app M) ((g ≫ h) ⁻¹ᵁ U)
        (modulesPullbackUnit (g ≫ h) M U s)
      = modulesPullbackUnit g ((Scheme.Modules.pullback h).obj M) (h ⁻¹ᵁ U)
          (modulesPullbackUnit h M U s) := by
  have h1 := CategoryTheory.unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction h).comp
      (Scheme.Modules.pullbackPushforwardAdjunction g))
    (Scheme.Modules.pullbackPushforwardAdjunction (g ≫ h))
    (Scheme.Modules.pullbackComp g h).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h1
  have h2 := congrArg (fun φ => Scheme.Modules.Hom.app φ U s) h1
  simp only [Scheme.Modules.Hom.comp_app, Adjunction.comp_unit_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforward_map_app] at h2
  exact h2.symm

/-- The unit of the module pullback is compatible with pseudofunctoriality: the constraint
`g^*(h^*M) ≅ (g ≫ h)^*M` carries the pullback of a section along `h` and then along `g` to its
pullback along `g ≫ h`. -/
theorem modulesPullbackUnit_pullbackComp_hom {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (s : Γ(M, U)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp g h).hom.app M) ((g ≫ h) ⁻¹ᵁ U)
        (modulesPullbackUnit g ((Scheme.Modules.pullback h).obj M) (h ⁻¹ᵁ U)
          (modulesPullbackUnit h M U s))
      = modulesPullbackUnit (g ≫ h) M U s := by
  have key : Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp g h).inv.app M)
        ((g ≫ h) ⁻¹ᵁ U) ≫
      Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp g h).hom.app M)
        ((g ≫ h) ⁻¹ᵁ U) = CategoryStruct.id _ := by
    rw [← Scheme.Modules.Hom.comp_app, ← NatTrans.comp_app,
      (Scheme.Modules.pullbackComp g h).inv_hom_id]
    rfl
  have h3 : ∀ z : Γ((Scheme.Modules.pullback (g ≫ h)).obj M, (g ≫ h) ⁻¹ᵁ U),
      Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp g h).hom.app M) ((g ≫ h) ⁻¹ᵁ U)
          (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp g h).inv.app M)
            ((g ≫ h) ⁻¹ᵁ U) z) = z :=
    fun z => congrArg (fun φ : Γ((Scheme.Modules.pullback (g ≫ h)).obj M, (g ≫ h) ⁻¹ᵁ U) ⟶
      Γ((Scheme.Modules.pullback (g ≫ h)).obj M, (g ≫ h) ⁻¹ᵁ U) => φ z) key
  exact Eq.trans (congrArg
      (fun z => Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp g h).hom.app M)
        ((g ≫ h) ⁻¹ᵁ U) z)
      (modulesPullbackUnit_pullbackComp_inv g h M U s).symm)
    (h3 (modulesPullbackUnit (g ≫ h) M U s))

/-- The action on sections of a composite of two isomorphisms of sheaves of modules: if the first
carries `s` to `t` and the second carries `t` to `r`, the composite carries `s` to `r`. -/
theorem modulesHomApp_trans {X : Scheme.{u}} {M N P : X.Modules} (e₁ : M ≅ N) (e₂ : N ≅ P)
    (U : X.Opens) {s : Γ(M, U)} {t : Γ(N, U)} {r : Γ(P, U)}
    (h₁ : Scheme.Modules.Hom.app e₁.hom U s = t)
    (h₂ : Scheme.Modules.Hom.app e₂.hom U t = r) :
    Scheme.Modules.Hom.app (e₁ ≪≫ e₂).hom U s = r := by
  subst h₁; subst h₂; rfl

/-- **The section-level action of `AlgebraicGeometry.Scheme.Modules.pullbackCongr`.** For equal
morphisms `f = g`, the induced identification `f ^* M ≅ g ^* M` carries the unit image over `f⁻¹U`
of a section `s` over `U` to the unit image over `g⁻¹U`, restricted along the equality of the two
preimage opens. -/
theorem modulesPullbackUnit_pullbackCongr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (hf : f = g)
    (M : Y.Modules) (U : Y.Opens) (s : Γ(M, U)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr hf).hom.app M) (f ⁻¹ᵁ U)
        (modulesPullbackUnit f M U s)
      = ((Scheme.Modules.pullback g).obj M).presheaf.map
          (eqToHom (show f ⁻¹ᵁ U = g ⁻¹ᵁ U by rw [hf])).op (modulesPullbackUnit g M U s) := by
  subst hf
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Scheme.Modules.Hom.id_app, eqToHom_refl, CategoryTheory.op_id]
  rw [CategoryTheory.Functor.map_id]

/-- **The section-level action of the inverse of
`AlgebraicGeometry.Scheme.Modules.pullbackCongr`.** For equal morphisms `f = g`, the induced
identification `g ^* M ≅ f ^* M` carries the unit image over `g⁻¹U` of a section `s` over `U` to
the unit image over `f⁻¹U`, restricted along the equality of the two preimage opens. -/
theorem modulesPullbackUnit_pullbackCongr_inv {X Y : Scheme.{u}} {f g : X ⟶ Y} (hf : f = g)
    (M : Y.Modules) (U : Y.Opens) (s : Γ(M, U)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr hf).inv.app M) (g ⁻¹ᵁ U)
        (modulesPullbackUnit g M U s)
      = ((Scheme.Modules.pullback f).obj M).presheaf.map
          (eqToHom (show g ⁻¹ᵁ U = f ⁻¹ᵁ U by rw [hf])).op (modulesPullbackUnit f M U s) := by
  subst hf
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_inv, NatTrans.id_app,
    Scheme.Modules.Hom.id_app, eqToHom_refl, CategoryTheory.op_id]
  rw [CategoryTheory.Functor.map_id]

/-- The identification of the pullbacks along two equal morphisms carries the unit image of a
global section along one to its unit image along the other: over the whole space the two preimage
opens are both `⊤`, so no restriction intervenes. -/
theorem modulesPullbackUnit_pullbackCongr_hom_top {X Y : Scheme.{u}} {f g : X ⟶ Y} (hf : f = g)
    (M : Y.Modules) (s : Γ(M, ⊤)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr hf).hom.app M) ⊤
        (modulesPullbackUnit f M ⊤ s) = modulesPullbackUnit g M ⊤ s := by
  subst hf; rfl

/-- The inverse of the identification of the pullbacks along two equal morphisms carries the unit
image of a global section along one to its unit image along the other. -/
theorem modulesPullbackUnit_pullbackCongr_inv_top {X Y : Scheme.{u}} {f g : X ⟶ Y} (hf : f = g)
    (M : Y.Modules) (s : Γ(M, ⊤)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr hf).inv.app M) ⊤
        (modulesPullbackUnit g M ⊤ s) = modulesPullbackUnit f M ⊤ s := by
  subst hf; rfl

/-- For `g ≫ h = k`, the identification `g ^* (h ^* M) ≅ k ^* M` carries the unit image of a
global section along `h` and then `g` to its unit image along `k`. -/
theorem modulesPullbackUnit_pullbackCompCongrIso_hom_top {X Y Z : Scheme.{u}} (g : X ⟶ Y)
    (h : Y ⟶ Z) {k : X ⟶ Z} (hk : g ≫ h = k) (M : Z.Modules) (s : Γ(M, ⊤)) :
    Scheme.Modules.Hom.app (pullbackCompCongrIso g h hk M).hom ⊤
        (modulesPullbackUnit g ((Scheme.Modules.pullback h).obj M) ⊤
          (modulesPullbackUnit h M ⊤ s))
      = modulesPullbackUnit k M ⊤ s := by
  subst hk
  exact modulesPullbackUnit_pullbackComp_hom g h M ⊤ s

/-- For `g ≫ h = k`, the identification `k ^* M ≅ g ^* (h ^* M)` carries the unit image of a
global section along `k` to its unit image along `h` and then `g`. -/
theorem modulesPullbackUnit_pullbackCompCongrIso_inv_top {X Y Z : Scheme.{u}} (g : X ⟶ Y)
    (h : Y ⟶ Z) {k : X ⟶ Z} (hk : g ≫ h = k) (M : Z.Modules) (s : Γ(M, ⊤)) :
    Scheme.Modules.Hom.app (pullbackCompCongrIso g h hk M).inv ⊤ (modulesPullbackUnit k M ⊤ s)
      = modulesPullbackUnit g ((Scheme.Modules.pullback h).obj M) ⊤
          (modulesPullbackUnit h M ⊤ s) := by
  subst hk
  exact modulesPullbackUnit_pullbackComp_inv g h M ⊤ s

open CategoryTheory.Limits in
/-- **The pullback of an external tensor product along a pair, on global sections.** For
`p : P ⟶ S`, `q : Q ⟶ S` and `j : X ⟶ P`, `j' : X ⟶ Q` agreeing over `S`, the identification of
the pullback of `F ⊠ G` along `X ⟶ P ×_S Q` with `j ^* F ⊗ j' ^* G` carries the pulled-back
section coming from the pure tensor of the unit images of `x` and `y` on `P ×_S Q` to the section
coming from the pure tensor of the unit images of `x` along `j` and of `y` along `j'`. -/
theorem pullbackLift_externalTensorProductIso_hom_modulesPullbackUnit
    {X S P Q : Scheme.{u}} (p : P ⟶ S) (q : Q ⟶ S) (j : X ⟶ P) (j' : X ⟶ Q)
    (hcomm : j ≫ p = j' ≫ q) (F : P.Modules) (G : Q.Modules) (x : Γ(F, ⊤)) (y : Γ(G, ⊤)) :
    Scheme.Modules.Hom.app (pullbackLift_externalTensorProductIso p q j j' hcomm F G).hom ⊤
        (modulesPullbackUnit (pullback.lift j j' hcomm) (externalTensorProduct p q F G) ⊤
          (toTensorSheafSection (pullback p q).toRingedSpace
            ((Scheme.Modules.pullback (pullback.fst p q)).obj F)
            ((Scheme.Modules.pullback (pullback.snd p q)).obj G) (Opposite.op ⊤)
            (modulesPullbackUnit (pullback.fst p q) F ⊤ x ⊗ₜ
              modulesPullbackUnit (pullback.snd p q) G ⊤ y)))
      = toTensorSheafSection X.toRingedSpace ((Scheme.Modules.pullback j).obj F)
          ((Scheme.Modules.pullback j').obj G) (Opposite.op ⊤)
          (modulesPullbackUnit j F ⊤ x ⊗ₜ modulesPullbackUnit j' G ⊤ y) :=
  let eA := pullbackCompCongrIso (pullback.lift j j' hcomm) (pullback.fst p q)
    (pullback.lift_fst j j' hcomm) F
  let eB := pullbackCompCongrIso (pullback.lift j j' hcomm) (pullback.snd p q)
    (pullback.lift_snd j j' hcomm) G
  (congrArg (fun z => Scheme.Modules.Hom.app (tensorSheafMapIso eA eB).hom ⊤ z)
      (schemePullbackTensorIso_hom_modulesPullbackUnit (pullback.lift j j' hcomm)
        ((Scheme.Modules.pullback (pullback.fst p q)).obj F)
        ((Scheme.Modules.pullback (pullback.snd p q)).obj G) ⊤
        (modulesPullbackUnit (pullback.fst p q) F ⊤ x)
        (modulesPullbackUnit (pullback.snd p q) G ⊤ y))).trans
    ((tensorSheafMapIso_hom_toTensorSheafSection eA eB ⊤ _ _).trans
      (congrArg₂ (fun (z : Γ((Scheme.Modules.pullback j).obj F, ⊤))
            (wz : Γ((Scheme.Modules.pullback j').obj G, ⊤)) =>
          toTensorSheafSection X.toRingedSpace ((Scheme.Modules.pullback j).obj F)
            ((Scheme.Modules.pullback j').obj G) (Opposite.op ⊤) (z ⊗ₜ wz))
        (modulesPullbackUnit_pullbackCompCongrIso_hom_top (pullback.lift j j' hcomm)
          (pullback.fst p q) (pullback.lift_fst j j' hcomm) F x)
        (modulesPullbackUnit_pullbackCompCongrIso_hom_top (pullback.lift j j' hcomm)
          (pullback.snd p q) (pullback.lift_snd j j' hcomm) G y)))

end Stacks.Tag01VSPullbackTensor

end
@[expose] public noncomputable section LocalSections

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

universe u

namespace Stacks.Tag01VSPullbackTensor

open Stacks.SheafOfModules.TensorStalkRingedSpace

/-! ### Sections over an arbitrary open -/

/-- Two successive restrictions of a section of a sheaf of modules are the restriction along the
composite: the opens of a scheme form a poset, so the composite is the only morphism there is. -/
theorem presheaf_map_map {X : Scheme.{u}} (M : X.Modules) {U V W : X.Opens}
    (i : V ⟶ U) (i' : W ⟶ V) (i'' : W ⟶ U) (s : Γ(M, U)) :
    M.presheaf.map i'.op (M.presheaf.map i.op s) = M.presheaf.map i''.op s := by
  rw [show i'' = i' ≫ i from Subsingleton.elim _ _, CategoryTheory.op_comp,
    CategoryTheory.Functor.map_comp]
  rfl

/-- A morphism of sheaves of modules commutes with restriction of sections. -/
theorem homApp_presheaf_map {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens}
    (i : V ⟶ U) (s : Γ(M, U)) :
    Scheme.Modules.Hom.app φ V (M.presheaf.map i.op s)
      = N.presheaf.map i.op (Scheme.Modules.Hom.app φ U s) := by
  have h := congrArg (fun f : M.presheaf.obj (.op U) ⟶ N.presheaf.obj (.op V) =>
    ConcreteCategory.hom f s) (φ.mapPresheaf.naturality i.op)
  simpa only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app] using h

/-- **The unit of the module pullback is natural in the open.** The unit image of a restricted
section is the restriction of the unit image, along the induced inclusion of preimages. -/
theorem modulesPullbackUnit_map {X Y : Scheme.{u}} (g : X ⟶ Y) (F : Y.Modules) {U V : Y.Opens}
    (hVU : V ≤ U) (s : Γ(F, U)) :
    modulesPullbackUnit g F V (F.presheaf.map (homOfLE hVU).op s)
      = ((Scheme.Modules.pullback g).obj F).presheaf.map
          (homOfLE (show g ⁻¹ᵁ V ≤ g ⁻¹ᵁ U from fun _ hz => hVU hz)).op
          (modulesPullbackUnit g F U s) :=
  homApp_presheaf_map ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F)
    (homOfLE hVU) s

/-- The global section of `g ^* F` attached to a section of `F` over an open `U` whose preimage is
the whole of the source: the unit image of the section, read over `⊤`. -/
def modulesPullbackUnitTop {X Y : Scheme.{u}} (g : X ⟶ Y) (F : Y.Modules) (U : Y.Opens)
    (hU : g ⁻¹ᵁ U = ⊤) (s : Γ(F, U)) : Γ((Scheme.Modules.pullback g).obj F, ⊤) :=
  ((Scheme.Modules.pullback g).obj F).presheaf.map (homOfLE hU.ge).op
    (modulesPullbackUnit g F U s)

/-- **For `g ≫ h = k`, the identification `g ^* (h ^* M) ≅ k ^* M` on sections over an arbitrary
open.** It carries the unit image of a section over `U` along `h` and then `g` to its unit image
along `k`, restricted along the equality of the two preimage opens. -/
theorem modulesPullbackUnit_pullbackCompCongrIso_hom {X Y Z : Scheme.{u}} (g : X ⟶ Y)
    (h : Y ⟶ Z) {k : X ⟶ Z} (hk : g ≫ h = k) (M : Z.Modules) (U : Z.Opens) (s : Γ(M, U)) :
    Scheme.Modules.Hom.app (pullbackCompCongrIso g h hk M).hom ((g ≫ h) ⁻¹ᵁ U)
        (modulesPullbackUnit g ((Scheme.Modules.pullback h).obj M) (h ⁻¹ᵁ U)
          (modulesPullbackUnit h M U s))
      = ((Scheme.Modules.pullback k).obj M).presheaf.map
          (eqToHom (show (g ≫ h) ⁻¹ᵁ U = k ⁻¹ᵁ U by rw [hk])).op
          (modulesPullbackUnit k M U s) :=
  modulesHomApp_trans _ _ _ (modulesPullbackUnit_pullbackComp_hom g h M U s)
    (modulesPullbackUnit_pullbackCongr_hom hk M U s)

/-- **For `g ≫ h = k`, the identification `k ^* M ≅ g ^* (h ^* M)` on sections over an arbitrary
open.** It carries the unit image of a section over `U` along `k` to its unit image along `h` and
then `g`, restricted along the equality of the two preimage opens. -/
theorem modulesPullbackUnit_pullbackCompCongrIso_inv {X Y Z : Scheme.{u}} (g : X ⟶ Y)
    (h : Y ⟶ Z) {k : X ⟶ Z} (hk : g ≫ h = k) (M : Z.Modules) (U : Z.Opens) (s : Γ(M, U)) :
    Scheme.Modules.Hom.app (pullbackCompCongrIso g h hk M).inv (k ⁻¹ᵁ U)
        (modulesPullbackUnit k M U s)
      = ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback h).obj M)).presheaf.map
          (eqToHom (show k ⁻¹ᵁ U = (g ≫ h) ⁻¹ᵁ U by rw [hk])).op
          (modulesPullbackUnit g ((Scheme.Modules.pullback h).obj M) (h ⁻¹ᵁ U)
            (modulesPullbackUnit h M U s)) := by
  subst hk
  simp only [eqToHom_refl, CategoryTheory.op_id]
  rw [CategoryTheory.Functor.map_id]
  exact modulesPullbackUnit_pullbackComp_inv g h M U s

/-- The canonical map into the sheaf tensor product commutes with restriction, on a pure
tensor. -/
theorem toTensorSheafSection_presheaf_map {X : Scheme.{u}} (A B : X.Modules) {U V : X.Opens}
    (i : V ⟶ U) (s : Γ(A, U)) (t : Γ(B, U)) :
    (Scheme.Modules.presheaf (X := X)
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩).obj (A)).obj (B)))).map i.op
        (toTensorSheafSection X.toRingedSpace A B (op U) (s ⊗ₜ t))
      = toTensorSheafSection X.toRingedSpace A B (op V)
          (A.presheaf.map i.op s ⊗ₜ B.presheaf.map i.op t) :=
  (PresheafOfModules.naturality_apply
    (sheafifyUnit X.toRingedSpace
      ((PresheafOfModules.tensorObj (O := (X.toRingedSpace).presheaf) (A.val) (B.val)))) i.op
    (s ⊗ₜ[X.presheaf.obj (op U)] t)).symm

/-! ### The section of an external tensor product attached to a pair of local sections -/

open CategoryTheory.Limits in
/-- **The section of `F ⊠ G` attached to a pair of local sections.** For `x` a section of `F` over
`U` and `y` a section of `G` over `V`, and any open `W` of `P ×_S Q` inside
`pr₁⁻¹U ∩ pr₂⁻¹V`, this is the section of `F ⊠ G` over `W` coming from the pure tensor of the
pullbacks of `x` and of `y`, restricted to `W`. It does not refer to any chart. -/
def externalTensorSection {S P Q : Scheme.{u}} (p : P ⟶ S) (q : Q ⟶ S) (F : P.Modules)
    (G : Q.Modules) {U : P.Opens} {V : Q.Opens} (x : Γ(F, U)) (y : Γ(G, V))
    (W : (pullback p q).Opens) (hW₁ : W ≤ pullback.fst p q ⁻¹ᵁ U)
    (hW₂ : W ≤ pullback.snd p q ⁻¹ᵁ V) :
    Γ(externalTensorProduct p q F G, W) :=
  toTensorSheafSection (pullback p q).toRingedSpace
    ((Scheme.Modules.pullback (pullback.fst p q)).obj F)
    ((Scheme.Modules.pullback (pullback.snd p q)).obj G) (op W)
    (((Scheme.Modules.pullback (pullback.fst p q)).obj F).presheaf.map (homOfLE hW₁).op
        (modulesPullbackUnit (pullback.fst p q) F U x) ⊗ₜ
      ((Scheme.Modules.pullback (pullback.snd p q)).obj G).presheaf.map (homOfLE hW₂).op
        (modulesPullbackUnit (pullback.snd p q) G V y))

/-- The identification `g ^* (h ^* M) ≅ k ^* M` carries the unit image along `g` of the restriction
to `W` of the unit image along `h` of a section over `U` to the restriction of its unit image
along `k`. -/
private theorem restrict_pullbackCompCongrIso_hom {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    {k : X ⟶ Z} (hk : g ≫ h = k) (M : Z.Modules) {U : Z.Opens} (W : Y.Opens)
    (hW : W ≤ h ⁻¹ᵁ U) (hj : g ⁻¹ᵁ W ≤ k ⁻¹ᵁ U) (s : Γ(M, U)) :
    Scheme.Modules.Hom.app (pullbackCompCongrIso g h hk M).hom (g ⁻¹ᵁ W)
        (modulesPullbackUnit g ((Scheme.Modules.pullback h).obj M) W
          (((Scheme.Modules.pullback h).obj M).presheaf.map (homOfLE hW).op
            (modulesPullbackUnit h M U s)))
      = ((Scheme.Modules.pullback k).obj M).presheaf.map (homOfLE hj).op
          (modulesPullbackUnit k M U s) := by
  have hW' : g ⁻¹ᵁ W ≤ g ⁻¹ᵁ (h ⁻¹ᵁ U) := fun _ hz => hW hz
  rw [modulesPullbackUnit_map, homApp_presheaf_map]
  exact (congrArg (((Scheme.Modules.pullback k).obj M).presheaf.map (homOfLE hW').op)
    (modulesPullbackUnit_pullbackCompCongrIso_hom g h hk M U s)).trans
      (presheaf_map_map _ _ _ _ _)

open CategoryTheory.Limits in
/-- **The pullback of an external tensor product along a pair, on sections over an arbitrary
open.** For `p : P ⟶ S`, `q : Q ⟶ S` and `j : X ⟶ P`, `j' : X ⟶ Q` agreeing over `S`, the
identification of the pullback of `F ⊠ G` along `X ⟶ P ×_S Q` with `j ^* F ⊗ j' ^* G` carries the
pulled-back section attached to `x` over `U` and `y` over `V` to the section coming from the pure
tensor of the unit images of `x` along `j` and of `y` along `j'`, each restricted to the preimage
of `W`. -/
theorem pullbackLift_externalTensorProductIso_hom_externalTensorSection
    {X S P Q : Scheme.{u}} (p : P ⟶ S) (q : Q ⟶ S) (j : X ⟶ P) (j' : X ⟶ Q)
    (hcomm : j ≫ p = j' ≫ q) (F : P.Modules) (G : Q.Modules) {U : P.Opens} {V : Q.Opens}
    (x : Γ(F, U)) (y : Γ(G, V)) (W : (pullback p q).Opens)
    (hW₁ : W ≤ pullback.fst p q ⁻¹ᵁ U) (hW₂ : W ≤ pullback.snd p q ⁻¹ᵁ V)
    (hj₁ : pullback.lift j j' hcomm ⁻¹ᵁ W ≤ j ⁻¹ᵁ U)
    (hj₂ : pullback.lift j j' hcomm ⁻¹ᵁ W ≤ j' ⁻¹ᵁ V) :
    Scheme.Modules.Hom.app (pullbackLift_externalTensorProductIso p q j j' hcomm F G).hom
        (pullback.lift j j' hcomm ⁻¹ᵁ W)
        (modulesPullbackUnit (pullback.lift j j' hcomm) (externalTensorProduct p q F G) W
          (externalTensorSection p q F G x y W hW₁ hW₂))
      = toTensorSheafSection X.toRingedSpace ((Scheme.Modules.pullback j).obj F)
          ((Scheme.Modules.pullback j').obj G) (op (pullback.lift j j' hcomm ⁻¹ᵁ W))
          (((Scheme.Modules.pullback j).obj F).presheaf.map (homOfLE hj₁).op
              (modulesPullbackUnit j F U x) ⊗ₜ
            ((Scheme.Modules.pullback j').obj G).presheaf.map (homOfLE hj₂).op
              (modulesPullbackUnit j' G V y)) := by
  have step1 := schemePullbackTensorIso_hom_modulesPullbackUnit (pullback.lift j j' hcomm)
    ((Scheme.Modules.pullback (pullback.fst p q)).obj F)
    ((Scheme.Modules.pullback (pullback.snd p q)).obj G) W
    (((Scheme.Modules.pullback (pullback.fst p q)).obj F).presheaf.map (homOfLE hW₁).op
      (modulesPullbackUnit (pullback.fst p q) F U x))
    (((Scheme.Modules.pullback (pullback.snd p q)).obj G).presheaf.map (homOfLE hW₂).op
      (modulesPullbackUnit (pullback.snd p q) G V y))
  have step2 := tensorSheafMapIso_hom_toTensorSheafSection
    (pullbackCompCongrIso (pullback.lift j j' hcomm) (pullback.fst p q)
      (pullback.lift_fst j j' hcomm) F)
    (pullbackCompCongrIso (pullback.lift j j' hcomm) (pullback.snd p q)
      (pullback.lift_snd j j' hcomm) G) (pullback.lift j j' hcomm ⁻¹ᵁ W)
    (modulesPullbackUnit (pullback.lift j j' hcomm)
      ((Scheme.Modules.pullback (pullback.fst p q)).obj F) W
      (((Scheme.Modules.pullback (pullback.fst p q)).obj F).presheaf.map (homOfLE hW₁).op
        (modulesPullbackUnit (pullback.fst p q) F U x)))
    (modulesPullbackUnit (pullback.lift j j' hcomm)
      ((Scheme.Modules.pullback (pullback.snd p q)).obj G) W
      (((Scheme.Modules.pullback (pullback.snd p q)).obj G).presheaf.map (homOfLE hW₂).op
        (modulesPullbackUnit (pullback.snd p q) G V y)))
  have step3a := restrict_pullbackCompCongrIso_hom (pullback.lift j j' hcomm) (pullback.fst p q)
    (pullback.lift_fst j j' hcomm) F W hW₁ hj₁ x
  have step3b := restrict_pullbackCompCongrIso_hom (pullback.lift j j' hcomm) (pullback.snd p q)
    (pullback.lift_snd j j' hcomm) G W hW₂ hj₂ y
  have step4 := congrArg₂
    (fun (z : Γ((Scheme.Modules.pullback j).obj F, pullback.lift j j' hcomm ⁻¹ᵁ W))
        (wz : Γ((Scheme.Modules.pullback j').obj G, pullback.lift j j' hcomm ⁻¹ᵁ W)) =>
      toTensorSheafSection X.toRingedSpace ((Scheme.Modules.pullback j).obj F)
        ((Scheme.Modules.pullback j').obj G) (op (pullback.lift j j' hcomm ⁻¹ᵁ W)) (z ⊗ₜ wz))
    step3a step3b
  exact modulesHomApp_trans _ _ _ step1 (step2.trans step4)

end Stacks.Tag01VSPullbackTensor

end LocalSections
