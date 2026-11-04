module

public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.PullbackSections

/-!
# Base change for the pullback-sections presheaf

The presheaf of Tag 03DS attached to a module `F` on a scheme `S` sends a scheme `T` over `S` to
`Γ(T, T.hom⁺ F)`.  If `X` is a scheme over `S`, every scheme over `X` is in particular a scheme
over `S`, and the resulting presheaf on `Over X.left` is the presheaf of Tag 03DS attached to the
base change `X.hom⁺ F` of `F` to `X.left`.  This file proves that, and deduces that the sheaf
condition for a covering family of `X` in `Over S` is the sheaf condition for the corresponding
family in `Over X.left` for the base-changed module.

This is the reduction "without loss of generality `X = S`" that both halves of Tag 03DT need: the
Zariski half and the single faithfully flat morphism of affines both concern covering families of
one object of the site, and after this reduction that object may be taken to be the base.
Combined with Stacks 01BG (`Stacks.Modules.isQuasicoherent_pullback`) the base-changed module is
again quasi-coherent, so the reduction stays inside the quasi-coherent world.

## Main definitions

* `Stacks.Sites.sectionsTopIso` turns an isomorphism of modules into an isomorphism of their
  groups of global sections.
* `Stacks.Sites.topUnitMap` is the map on global sections induced by the unit of the
  pullback--pushforward adjunction followed by a comparison map; it is the shape of
  `AlgebraicGeometry.pullbackSectionsMap`.
* `Stacks.Sites.pullbackSectionsBaseChangeIso` is the base-change isomorphism: the restriction
  along `CategoryTheory.Over.map X.hom` of the Tag 03DS presheaf of `F` is the Tag 03DS presheaf
  of `X.hom⁺ F`.

## Main results

* `Stacks.Sites.pullbackComp_assoc_app`: the associativity coherence of the pullback
  pseudofunctor, in the form needed to compare iterated pullbacks along `T → X → S`.
* `Stacks.Sites.pullbackSectionsMap_baseChange`: the base-change comparison is compatible with
  the maps of the Tag 03DS presheaf.
* `Stacks.Sites.isSheafFor_baseChange_iff`: the sheaf condition for a sieve of `Over X.left` on
  its terminal object, for the Tag 03DS presheaf of `X.hom⁺ F`, is the sheaf condition for the
  pushed-forward sieve of `Over S`, for the Tag 03DS presheaf of `F`.
* `Stacks.Sites.isSheafFor_overEquiv_symm_baseChange_iff`: the same statement for the sieves
  attached to a sieve of the scheme `X.left`, which is the form the reduction of Tag 03DT uses.

## Implementation notes

Every statement here is about `AlgebraicGeometry.PullbackSectionsPresheaf`, the structure that
packages a functor on `(Over S)ᵒᵖ` together with identifications of its values with
`Γ(T, T.hom⁺ F)` under which its maps are `AlgebraicGeometry.pullbackSectionsMap`.  Working with
the structure rather than with `AlgebraicGeometry.quasiCoherentPresheafFunctor` costs nothing and
removes the quasi-coherence hypothesis from the statements, which is not used by any of them.

Two technical points recur.  First, `Γ((Scheme.Modules.pushforward j).obj N, ⊤)` and `Γ(N, ⊤)` are
definitionally equal, but only after unfolding `AlgebraicGeometry.Scheme.Modules.pushforward`;
consequently `rw` fails on any composite in which the identification is implicit, because its
motive check runs at `implicit` transparency.  Every lemma about `Stacks.Sites.topUnitMap` is
therefore proved by rewriting the underlying morphism *of modules* — where no such identification
occurs — and concluding by `rfl`.  Second, the comparison map for a morphism `n` of `Over X.left`
depends on `n` only through `n.left` and `CategoryTheory.Over.w n`; the proof of
`Stacks.Sites.pullbackSectionsMap_baseChange` substitutes the latter, which is possible only after
the structure morphism of the source has been exposed as a variable, and that is why the lemma is
stated for `CategoryTheory.Over.mk` and `CategoryTheory.Over.homMk`.

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Stacks.Sites

section Modules

variable {T T₁ T₂ : Scheme.{u}}

/-- An isomorphism of modules induces an isomorphism of their groups of global sections. -/
noncomputable def sectionsTopIso {M N : T.Modules} (e : M ≅ N) : Γ(M, ⊤) ≅ Γ(N, ⊤) where
  hom := e.hom.app ⊤
  inv := e.inv.app ⊤
  hom_inv_id := by rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]
  inv_hom_id := by rw [← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app]

/-- The forward map of `Stacks.Sites.sectionsTopIso e` is the global-sections component of `e.hom`.
-/
@[simp]
lemma sectionsTopIso_hom {M N : T.Modules} (e : M ≅ N) :
    (sectionsTopIso e).hom = e.hom.app ⊤ := rfl

/-- The inverse map of `Stacks.Sites.sectionsTopIso e` is the global-sections component of `e.inv`.
-/
@[simp]
lemma sectionsTopIso_inv {M N : T.Modules} (e : M ≅ N) :
    (sectionsTopIso e).inv = e.inv.app ⊤ := rfl

/-- The map on global sections attached to a morphism `j : T₁ ⟶ T₂` of schemes, a module `M` on
`T₂`, a module `N` on `T₁` and a comparison `j⁺ M ⟶ N`: the unit of the pullback--pushforward
adjunction, taken on global sections.  This is the shape of
`AlgebraicGeometry.pullbackSectionsMap`, which is the case where `N` is a pullback of a module on
a common base and the comparison is the canonical one. -/
noncomputable def topUnitMap (j : T₁ ⟶ T₂) {M : T₂.Modules} {N : T₁.Modules}
    (a : (Scheme.Modules.pullback j).obj M ⟶ N) : Γ(M, ⊤) ⟶ Γ(N, ⊤) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M ≫
    (Scheme.Modules.pushforward j).map a).app ⊤

/-- Postcomposing `Stacks.Sites.topUnitMap` with the global sections of a morphism of modules
amounts to postcomposing its comparison map. -/
lemma topUnitMap_comp (j : T₁ ⟶ T₂) {M : T₂.Modules} {N N' : T₁.Modules}
    (a : (Scheme.Modules.pullback j).obj M ⟶ N) (e : N ⟶ N') :
    topUnitMap j a ≫ e.app ⊤ = topUnitMap j (a ≫ e) := by
  rw [topUnitMap, topUnitMap, Functor.map_comp, ← Category.assoc]
  rfl

/-- Precomposing `Stacks.Sites.topUnitMap` with the global sections of a morphism of modules
amounts to precomposing its comparison map with the pullback of that morphism. -/
lemma comp_topUnitMap (j : T₁ ⟶ T₂) {M M' : T₂.Modules} {N : T₁.Modules} (d : M ⟶ M')
    (a : (Scheme.Modules.pullback j).obj M' ⟶ N) :
    d.app ⊤ ≫ topUnitMap j a = topUnitMap j ((Scheme.Modules.pullback j).map d ≫ a) := by
  have hn := (Scheme.Modules.pullbackPushforwardAdjunction j).unit.naturality d
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [topUnitMap, topUnitMap, Functor.map_comp, ← Category.assoc, ← hn, Category.assoc]
  rfl

/-- The associativity coherence of the pullback pseudofunctor, in the form that compares the
two ways of identifying `f⁺ g⁺ h⁺ M` with `(f ≫ g ≫ h)⁺ M`. -/
lemma pullbackComp_assoc_app {A B C D : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D)
    (M : D.Modules) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app M) ≫
        (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) =
      (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M ≫
        (Scheme.Modules.pullbackCongr (Category.assoc f g h).symm).hom.app M ≫
        (Scheme.Modules.pullbackComp (f ≫ g) h).inv.app M := by
  have hassoc := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity f g h) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, eqToHom_app] at hassoc
  have key := congrArg (fun t => (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M ≫ t ≫
    (Scheme.Modules.pullbackComp (f ≫ g) h).inv.app M) hassoc
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app,
    Category.comp_id] at key
  rw [key]
  simp [Scheme.Modules.pullbackCongr]

end Modules

section BaseChange

variable {S : Scheme.{u}} (F : S.Modules) (X : Over S)

/-- The canonical comparison on global sections for a scheme `A` over `X.left`: the sections of
the pullback of `F` along the composite `A.left ⟶ X.left ⟶ S` are the sections of the pullback
along `A.left ⟶ X.left` of the base change `X.hom⁺ F`. -/
noncomputable def baseChangeSectionsIso (A : Over X.left) :
    Γ((Scheme.Modules.pullback ((Over.map X.hom).obj A).hom).obj F, ⊤) ≅
      Γ((Scheme.Modules.pullback A.hom).obj ((Scheme.Modules.pullback X.hom).obj F), ⊤) :=
  sectionsTopIso ((Scheme.Modules.pullbackComp A.hom X.hom).app F).symm

/-- The forward map of `Stacks.Sites.baseChangeSectionsIso` is the global-sections component of the
inverse of the pullback composition isomorphism. -/
@[simp]
lemma baseChangeSectionsIso_hom (A : Over X.left) :
    (baseChangeSectionsIso F X A).hom =
      ((Scheme.Modules.pullbackComp A.hom X.hom).inv.app F).app ⊤ := rfl

/-- `AlgebraicGeometry.pullbackSectionsMap` is an instance of `Stacks.Sites.topUnitMap`. -/
lemma pullbackSectionsMap_eq_topUnitMap {A B : Over S} (g : A ⟶ B) :
    pullbackSectionsMap F g =
      topUnitMap g.left ((Scheme.Modules.pullbackComp g.left B.hom).hom.app F ≫
        (Scheme.Modules.pullbackCongr (Over.w g)).hom.app F) := by
  rw [topUnitMap, pullbackSectionsMap]
  exact congrArg _ (((Scheme.Modules.pullback A.hom).obj F).presheaf.map_id _)

/-- The base-change comparison of `Stacks.Sites.baseChangeSectionsIso` is compatible with the
maps of the Tag 03DS presheaf: for a morphism of schemes over `X.left`, the square formed by the
two comparison isomorphisms and the two pullback maps on sections commutes.  Stated for
`CategoryTheory.Over.mk` and `CategoryTheory.Over.homMk` so that the structure morphism of the
source is a variable and can be eliminated. -/
lemma pullbackSectionsMap_baseChange_mk {A₀ B₀ : Scheme.{u}} (j : A₀ ⟶ B₀) (h₂ : B₀ ⟶ X.left)
    (h₁ : A₀ ⟶ X.left) (hw : j ≫ h₂ = h₁) :
    pullbackSectionsMap F ((Over.map X.hom).map
          (Over.homMk j hw : Over.mk h₁ ⟶ Over.mk h₂)) ≫
        (baseChangeSectionsIso F X (Over.mk h₁)).hom =
      (baseChangeSectionsIso F X (Over.mk h₂)).hom ≫
        pullbackSectionsMap ((Scheme.Modules.pullback X.hom).obj F)
          (Over.homMk j hw : Over.mk h₁ ⟶ Over.mk h₂) := by
  subst hw
  rw [pullbackSectionsMap_eq_topUnitMap, pullbackSectionsMap_eq_topUnitMap,
    baseChangeSectionsIso_hom, baseChangeSectionsIso_hom, topUnitMap_comp, comp_topUnitMap]
  refine congrArg (topUnitMap j) ?_
  simp only [Category.assoc]
  show (Scheme.Modules.pullbackComp j (h₂ ≫ X.hom)).hom.app F ≫
        (Scheme.Modules.pullbackCongr (Category.assoc j h₂ X.hom).symm).hom.app F ≫
        (Scheme.Modules.pullbackComp (j ≫ h₂) X.hom).inv.app F =
      (Scheme.Modules.pullback j).map ((Scheme.Modules.pullbackComp h₂ X.hom).inv.app F) ≫
        (Scheme.Modules.pullbackComp j h₂).hom.app ((Scheme.Modules.pullback X.hom).obj F) ≫
        (Scheme.Modules.pullbackCongr (rfl : j ≫ h₂ = j ≫ h₂)).hom.app
          ((Scheme.Modules.pullback X.hom).obj F)
  rw [show (Scheme.Modules.pullbackCongr (rfl : j ≫ h₂ = j ≫ h₂)).hom.app
      ((Scheme.Modules.pullback X.hom).obj F) = 𝟙 _ from rfl, Category.comp_id]
  exact (pullbackComp_assoc_app j h₂ X.hom F).symm

/-- The base-change comparison is compatible with the maps of the Tag 03DS presheaf, for an
arbitrary morphism of schemes over `X.left`. -/
lemma pullbackSectionsMap_baseChange {A B : Over X.left} (n : A ⟶ B) :
    pullbackSectionsMap F ((Over.map X.hom).map n) ≫ (baseChangeSectionsIso F X A).hom =
      (baseChangeSectionsIso F X B).hom ≫
        pullbackSectionsMap ((Scheme.Modules.pullback X.hom).obj F) n :=
  pullbackSectionsMap_baseChange_mk F X n.left B.hom A.hom (Over.w n)

/-- The maps of a `AlgebraicGeometry.PullbackSectionsPresheaf`, read off from its identifications
with groups of global sections. -/
lemma PullbackSectionsPresheaf.functor_map (P : PullbackSectionsPresheaf S F)
    {A B : (Over S)ᵒᵖ} (g : A ⟶ B) :
    P.functor.map g =
      (P.objIso A).hom ≫ pullbackSectionsMap F g.unop ≫ (P.objIso B).inv := by
  rw [← P.map_objIso g]
  simp

/-- **Base change for the presheaf of Tag 03DS.**  The restriction along
`CategoryTheory.Over.map X.hom` of the presheaf `(T ⟶ S) ↦ Γ(T, T.hom⁺ F)` on the schemes over
`S` is the presheaf `(A ⟶ X.left) ↦ Γ(A, A.hom⁺ (X.hom⁺ F))` on the schemes over `X.left`. -/
noncomputable def pullbackSectionsBaseChangeIso (P : PullbackSectionsPresheaf S F)
    (Q : PullbackSectionsPresheaf X.left ((Scheme.Modules.pullback X.hom).obj F)) :
    (Over.map X.hom).op ⋙ P.functor ≅ Q.functor :=
  NatIso.ofComponents
    (fun A => P.objIso (op ((Over.map X.hom).obj A.unop)) ≪≫
      baseChangeSectionsIso F X A.unop ≪≫ (Q.objIso A).symm)
    (fun {A B} m => by
      have h := pullbackSectionsMap_baseChange F X m.unop
      dsimp only [Functor.comp_map, Functor.op_map, Functor.op_obj, Quiver.Hom.unop_op,
        Iso.trans_hom, Iso.symm_hom]
      rw [PullbackSectionsPresheaf.functor_map, PullbackSectionsPresheaf.functor_map]
      simp only [Quiver.Hom.unop_op, Category.assoc, Iso.inv_hom_id_assoc]
      rw [reassoc_of% h])

end BaseChange

section SheafCondition

variable {S : Scheme.{u}} (F : S.Modules) (X : Over S)

/-- **The sheaf condition for the presheaf of Tag 03DS is a statement about the base.**  For a
sieve `R` on the terminal object of the schemes over `X.left`, the sheaf condition for the
Tag 03DS presheaf of the base change `X.hom⁺ F` is the sheaf condition, for the Tag 03DS presheaf
of `F` on the schemes over `S`, for the sieve obtained from `R` by pushing forward along
`CategoryTheory.Over.map X.hom`.

Together with Stacks 01BG, which says that `X.hom⁺ F` is again quasi-coherent, this is the
reduction of Tag 03DT to covering families of the base. -/
theorem isSheafFor_baseChange_iff (P : PullbackSectionsPresheaf S F)
    (Q : PullbackSectionsPresheaf X.left ((Scheme.Modules.pullback X.hom).obj F))
    (R : Sieve (Over.mk (𝟙 X.left) : Over X.left)) {X' : Over S}
    (e : (Over.map X.hom).obj (Over.mk (𝟙 X.left)) ≅ X') :
    Presieve.IsSheafFor (Q.functor ⋙ CategoryTheory.forget AddCommGrpCat) R.arrows ↔
      Presieve.IsSheafFor (P.functor ⋙ CategoryTheory.forget AddCommGrpCat)
        (Sieve.pullback e.inv (Sieve.functorPushforward (Over.map X.hom) R)).arrows := by
  rw [← Presieve.isSheafFor_over_map_op_comp_iff X.hom
    (P.functor ⋙ CategoryTheory.forget AddCommGrpCat) R e]
  exact (Presieve.isSheafFor_iff_of_iso (Functor.isoWhiskerRight
    (pullbackSectionsBaseChangeIso F X P Q) (CategoryTheory.forget AddCommGrpCat))).symm

/-- Pushing a sieve of `X.left` forward to the terminal object of the schemes over `X.left`, then
along `CategoryTheory.Over.map X.hom`, and pulling it back to `X`, gives the sieve of `X` it came
from. -/
lemma pullback_overEquiv_symm_over_map (T : Sieve X.left) :
    Sieve.pullback (Over.isoMk (Iso.refl X.left) :
          (Over.map X.hom).obj (Over.mk (𝟙 X.left)) ≅ X).inv
        (Sieve.functorPushforward (Over.map X.hom)
          ((Sieve.overEquiv (Over.mk (𝟙 X.left) : Over X.left)).symm T)) =
      (Sieve.overEquiv X).symm T := by
  rw [Sieve.functorPushforward_over_map]
  ext Z g
  simp

/-- **The sheaf condition for the presheaf of Tag 03DS is a statement about the base**, in the
form used downstream: for a sieve `T` of `X.left`, the sheaf condition for the Tag 03DS presheaf
of the base change `X.hom⁺ F` and the sieve of `Over X.left` corresponding to `T` is the sheaf
condition for the Tag 03DS presheaf of `F` and the sieve of `Over S` corresponding to `T`. -/
theorem isSheafFor_overEquiv_symm_baseChange_iff (P : PullbackSectionsPresheaf S F)
    (Q : PullbackSectionsPresheaf X.left ((Scheme.Modules.pullback X.hom).obj F))
    (T : Sieve X.left) :
    Presieve.IsSheafFor (Q.functor ⋙ CategoryTheory.forget AddCommGrpCat)
        ((Sieve.overEquiv (Over.mk (𝟙 X.left) : Over X.left)).symm T).arrows ↔
      Presieve.IsSheafFor (P.functor ⋙ CategoryTheory.forget AddCommGrpCat)
        ((Sieve.overEquiv X).symm T).arrows := by
  rw [isSheafFor_baseChange_iff F X P Q _
    (Over.isoMk (Iso.refl X.left) : (Over.map X.hom).obj (Over.mk (𝟙 X.left)) ≅ X),
    pullback_overEquiv_symm_over_map]

end SheafCondition

end Stacks.Sites

end
