module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposLowerShriekUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.CategoryTheory.Sites.Point.Topos
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.LeftExact
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The direct image of modules from a ringed point is exact, and the counit is the canonical
surjection

Let `(Sh(C), O)` be a ringed topos and `p` a point of it, and let `(Sh(pt), O_p)` be the
ringed point over `p` as in `Stacks.Sheaves.RingedPoint.RingedPointSituation`. This file proves
that the direct image `p_* : Mod(O_p) ⥤ Mod(O)` is exact, that the counit of the
adjunction `p^* ⊣ p_*` on modules is a surjection, and that this counit is, on underlying
sheaves, the canonical surjection `p⁻¹p_*M ⟶ M` of Stacks 05V7 — so that the latter is
`O_p`-linear.

Left exactness is formal: `p_*` is the right adjoint half of the morphism of ringed topoi, so
the underlying-sheaf functor turns it into the direct image of sheaves of sets, which preserves
all limits. The underlying-sheaf functor `Mod(O) ⥤ Sh(C)` reflects finite limits, so `p_*`
preserves them.

Right exactness is where the point is used: a section of a sheaf on the point is a set, and
every epimorphism of sets splits, so the direct image along `p` preserves epimorphisms. Hence
`p_*` preserves epimorphisms, and a functor between abelian categories that preserves
epimorphisms and kernels preserves homology, hence finite colimits.

Surjectivity of the counit `p^*p_*M ⟶ M` is the other half of the source's statement. It is an
epimorphism because `p_*` is faithful: on sets every counit component of `p^* ⊣ p_*` is
surjective, so the direct image of sheaves of sets is faithful, and the direct image of modules
becomes that functor after passing to underlying sheaves. That the map is a morphism of sheaves
of modules is built into its being the counit of the module adjunction of Stacks 03D7; what the
source asserts, and what `pullbackPushforwardModules_counit_stalk` proves, is that the map so
obtained *is* the canonical surjection `p⁻¹p_*M ⟶ M` of Stacks 05V7, which is the counit of
`p⁻¹ ⊣ p_*`.

That identification is the source's "`p^{-1} = p^*`". It is proved in two steps. On underlying
sheaves the counit of the module adjunction is the counit of `f⁻¹ ⊣ f_*` for the morphism of
topoi `f` out of the ringed point: the module adjunction is the inverse image of modules of
Stacks 03D3 followed by extension of scalars along `f♯`, the first factor contributes a counit
which on underlying sheaves is the one of `f⁻¹ ⊣ f_*`, and the second contributes the counit of
a restriction of scalars along an isomorphism, which is the identity on underlying sheaves. Then
the counit of `f⁻¹ ⊣ f_*`, read through `Sh(pt) = Sets`, is the counit of `p⁻¹ ⊣ p_*`, because
`p⁻¹` is a left adjoint of both `p_*` and of the direct image along the ringed point, and a
functor's right adjoints are canonically identified.

## Main results

* `Stacks.Sheaves.RingedPoint.preservesFiniteLimits_moduleSheafFunctor` and
  `reflectsFiniteLimits_moduleSheafFunctor`: the underlying-sheaf-of-sets functor on sheaves of
  modules preserves and reflects finite limits.
* `Stacks.Sheaves.RingedPoint.preservesEpimorphisms_moduleSheafFunctor`: it also preserves
  epimorphisms.
* `Stacks.Sheaves.RingedPoint.RingedPointSituation.pushforwardModulesUnderlyingIso`: the
  underlying sheaf of a direct image of modules is the direct image of the underlying sheaf.
* `Stacks.Sheaves.RingedPoint.RingedPointSituation.pushforwardModules_exact`: `p_*` is exact.
* `Stacks.Sheaves.RingedPoint.RingedPointSituation.pullbackPushforwardModules_counit_epi`: the
  counit `p^*p_*M ⟶ M` of the adjunction of Stacks 03D7 is a surjection of `O_p`-modules.
* `Stacks.Sheaves.RingedPoint.RingedPointSituation.pullbackPushforwardModules_counit_underlying`:
  on underlying sheaves that counit is the counit of the adjunction of the morphism of topoi out
  of the ringed point.
* `Stacks.Sheaves.RingedPoint.RingedPointSituation.pullbackPushforwardModules_counit_stalk`: read
  on sets it is the counit `p⁻¹p_*M ⟶ M` of the point, the canonical surjection of Stacks 05V7;
  this is the `O_p`-linearity that Stacks 05V8 part (2) asserts.
* `Stacks.Sheaves.RingedPoint.comp_counit_app_of_leftAdjointUniq` and
  `Stacks.Sheaves.RingedPoint.equivalence_functor_map_counit_app`: the two formal ingredients,
  about the counit of a composite adjunction and about transporting a counit along an
  equivalence of the target and uniqueness of right adjoints.

## Implementation notes

`Sheaf.moduleSheafFunctor` is the underlying-sheaf-of-sets functor, i.e. `SheafOfModules.toSheaf`
followed by the forgetful functor on abelian sheaves; this is the functor the source writes as
"the underlying sheaf of sets". Its `GrothendieckTopology.HasSheafCompose` hypothesis is
carried explicitly, since for a general site it is not automatic.

`RingedPointSituation` carries the `HasSheafCompose` instances for the site of the point as
fields, but not weak sheafification of abelian presheaves on that site nor the identification
of its inverted maps with the locally bijective ones; those are therefore hypotheses here. They
are what makes `Mod(O_p)` abelian, which the exactness statement needs in order to be about
homology at all.

The identification of the skyscraper functor of the point with the direct image along the ringed
point used in `pullbackPushforwardModules_counit_stalk` is
`Stacks.Sheaves.RingedPoint.RingedPointSituation.pointPushforwardIso`, the comparison of two
right adjoints of `p⁻¹`, and not the field `pushforwardIso` of the situation: the field is data
and says nothing about the adjunctions, whereas the counit statement is about them.

## References

* [Stacks Project, Tag 05V7](https://stacks.math.columbia.edu/tag/05V7)
* [Stacks Project, Tag 05V8](https://stacks.math.columbia.edu/tag/05V8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace Stacks.Sheaves.RingedPoint

universe v u w vₚ uₚ

section ModuleSheafFunctor

variable {T : Type u} [Category.{v} T] (J : GrothendieckTopology T)
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (R : Sheaf J RingCat.{w})

/-- The underlying sheaf of sets of a sheaf of modules preserves finite limits: it is
`SheafOfModules.toSheaf` followed by the forgetful functor on abelian sheaves, and the latter
preserves finite limits because it does so after passing to presheaves, where it is the
pointwise forgetful functor. -/
lemma preservesFiniteLimits_moduleSheafFunctor :
    PreservesFiniteLimits (Sheaf.moduleSheafFunctor R) := by
  have hcomp : PreservesFiniteLimits
      (sheafCompose J (forget AddCommGrpCat.{w}) ⋙ sheafToPresheaf J (Type w)) := by
    show PreservesFiniteLimits
      (sheafToPresheaf J AddCommGrpCat.{w} ⋙
        (whiskeringRight _ _ _).obj (forget AddCommGrpCat.{w}))
    infer_instance
  have : PreservesFiniteLimits (sheafCompose J (forget AddCommGrpCat.{w})) :=
    preservesFiniteLimits_of_reflects_of_preserves
      (sheafCompose J (forget AddCommGrpCat.{w})) (sheafToPresheaf J (Type w))
  show PreservesFiniteLimits
    (SheafOfModules.toSheaf.{w} R ⋙ sheafCompose J (forget AddCommGrpCat.{w}))
  exact comp_preservesFiniteLimits _ _

/-- The underlying sheaf of sets of a sheaf of modules reflects finite limits: it preserves
them, and `SheafOfModules.toSheaf` reflects isomorphisms. -/
lemma reflectsFiniteLimits_moduleSheafFunctor :
    ReflectsFiniteLimits (Sheaf.moduleSheafFunctor R) := by
  have : PreservesFiniteLimits (Sheaf.moduleSheafFunctor R) :=
    preservesFiniteLimits_moduleSheafFunctor J R
  have : (SheafOfModules.toSheaf.{w} R).ReflectsIsomorphisms := inferInstance
  show ReflectsFiniteLimits
    (SheafOfModules.toSheaf.{w} R ⋙ sheafCompose J (forget AddCommGrpCat.{w}))
  infer_instance

/-- The underlying sheaf of sets of a sheaf of modules preserves epimorphisms: an epimorphism
of sheaves of modules is locally surjective, local surjectivity is preserved by composing with
a forgetful functor, and a locally surjective map of sheaves is an epimorphism. -/
lemma preservesEpimorphisms_moduleSheafFunctor
    [J.HasSheafCompose (forget (Type w))]
    [HasSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] :
    PreservesEpimorphisms (Sheaf.moduleSheafFunctor R) := by
  show PreservesEpimorphisms
    (SheafOfModules.toSheaf.{w} R ⋙ sheafCompose J (forget AddCommGrpCat.{w}))
  constructor
  intro M N f hf
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{w} R) :=
    Stacks.SheafOfModules.instPreservesFiniteColimitsToSheaf R
  have h_epi : Epi ((SheafOfModules.toSheaf.{w} R).map f) := inferInstance
  have hloc : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf.{w} R).map f) :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{w}
      ((SheafOfModules.toSheaf.{w} R).map f)).2 h_epi
  have : Sheaf.IsLocallySurjective
      ((sheafCompose J (forget AddCommGrpCat.{w})).map
        ((SheafOfModules.toSheaf.{w} R).map f)) := inferInstance
  exact Sheaf.epi_of_isLocallySurjective
    ((sheafCompose J (forget AddCommGrpCat.{w})).map
      ((SheafOfModules.toSheaf.{w} R).map f))

end ModuleSheafFunctor

/-- **The counit of a composite adjunction, read through uniqueness of left adjoints.** If `E'`
is a second left adjoint of the right-hand functor `I`, then the counit of `F ⋙ E ⊣ I ⋙ G` is
the comparison `E ≅ E'` followed by `E'` of the counit of `F ⊣ G` and the counit of `E' ⊣ I`.
This is how the counit of the pullback-pushforward adjunction of modules is computed at a ringed
point: there the second left adjoint is restriction of scalars along the inverse of the structure
map, whose counit is the identity on underlying sheaves. -/
theorem comp_counit_app_of_leftAdjointUniq {A B C : Type*} [Category A] [Category B]
    [Category C] {F : A ⥤ B} {G : B ⥤ A} {E E' : B ⥤ C} {I : C ⥤ B}
    (adj₁ : F ⊣ G) (adj₂ : E ⊣ I) (adj₂' : E' ⊣ I) (Z : C) :
    (adj₁.comp adj₂).counit.app Z =
      (adj₂.leftAdjointUniq adj₂').hom.app (F.obj (G.obj (I.obj Z))) ≫
        E'.map (adj₁.counit.app (I.obj Z)) ≫ adj₂'.counit.app Z := by
  have e1 : (adj₁.comp adj₂).counit.app Z =
      E.map (adj₁.counit.app (I.obj Z)) ≫ adj₂.counit.app Z := by
    simp [Adjunction.comp]
  have hn := (adj₂.leftAdjointUniq adj₂').hom.naturality (adj₁.counit.app (I.obj Z))
  simp only [Functor.id_obj, Functor.comp_obj] at hn
  rw [e1, ← Adjunction.leftAdjointUniq_hom_app_counit adj₂ adj₂' Z, ← Category.assoc, hn,
    Category.assoc]

/-- **The counit of an adjunction composed with an equivalence of the target, read through
uniqueness of right adjoints.** If `F ⋙ e.functor` is identified with a functor `L` which is
itself a left adjoint, then the image under `e.functor` of the counit of `F ⊣ G` is the canonical
comparison followed by the counit of `L ⊣ R`, the comparison being built from the unit of `e`,
the given identification, and the unique identification of `R` with `e.inverse ⋙ G` as right
adjoints of `L`.

For a point of a ringed topos this says that the counit of the morphism of topoi out of the
ringed point, read on sets, is the counit `p⁻¹p_* ⟶ id` of the point. -/
theorem equivalence_functor_map_counit_app {C D E : Type*} [Category C] [Category D]
    [Category E] {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) (e : D ≌ E) {L : C ⥤ E}
    (iso : F ⋙ e.functor ≅ L) {R : E ⥤ C} (a' : L ⊣ R) (A : D) :
    e.functor.map (a.counit.app A) =
      e.functor.map (F.map (G.map (e.unitIso.hom.app A))) ≫
        iso.hom.app (G.obj (e.inverse.obj (e.functor.obj A))) ≫
          L.map ((Adjunction.rightAdjointUniq
              (Adjunction.ofNatIsoLeft (a.comp e.toAdjunction) iso) a').hom.app
            (e.functor.obj A)) ≫
            a'.counit.app (e.functor.obj A) := by
  rw [Adjunction.rightAdjointUniq_hom_app_counit
    (Adjunction.ofNatIsoLeft (a.comp e.toAdjunction) iso) a' (e.functor.obj A)]
  simp only [comp_obj, id_obj, Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
    whiskerLeft_app, Adjunction.comp_counit_app, Equivalence.toAdjunction_counit,
    Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc, ← e.functor.map_comp, a.counit_naturality, e.functor.map_comp,
    Category.assoc]
  simp

/-- Four morphisms composed before a fifth, reassociated. -/
private theorem comp_assoc₅ {C : Type*} [Category C] {V W X Y Z T : C}
    (a : V ⟶ W) (b : W ⟶ X) (c : X ⟶ Y) (d : Y ⟶ Z) (k : Z ⟶ T) :
    a ≫ b ≫ c ≫ d ≫ k = (a ≫ b ≫ c ≫ d) ≫ k := by
  simp

/-- A functor out of a category in which every epimorphism splits preserves epimorphisms. -/
lemma preservesEpimorphisms_of_splitEpiCategory
    {A B : Type*} [Category A] [Category B] [SplitEpiCategory A] (F : A ⥤ B) :
    PreservesEpimorphisms F := by
  constructor
  intro X Y f hf
  have : IsSplitEpi f := isSplitEpi_of_epi f
  infer_instance

open AlgebraicGeometry Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPushforward

namespace RingedPointSituation

variable {X : RingedTopos.{v, u, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {p : PointOfTopos.{w, v, u} X.J}
  (s : RingedPointSituation.{v, u, w, vₚ, uₚ} X p)

/-- The underlying sheaf of sets of the direct image of a sheaf of modules along the morphism
of ringed topoi out of the ringed point is the direct image of the underlying sheaf of sets,
naturally in the module. -/
def pushforwardModulesUnderlyingIso :
    pushforwardModules s.toRingedToposHom ⋙
        Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≅
      Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O) ⋙
        s.toRingedToposHom.toToposHom.pushforward :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by
    simp only [Functor.comp_map]
    apply moduleSheafFunctor_map_directImageModules_map)

/-- **Stacks 05V8.** The direct image of modules from a ringed point is exact. -/
@[stacks 05V8 "exactness of the direct image"]
theorem pushforwardModules_exact
    [HasWeakSheafify s.point.J AddCommGrpCat.{w}]
    [s.point.J.WEqualsLocallyBijective AddCommGrpCat.{w}] :
    exactFunctor
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O))
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (pushforwardModules s.toRingedToposHom) := by
  have : HasSheafify s.point.J AddCommGrpCat.{w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let F := pushforwardModules s.toRingedToposHom
  let Uₚ := Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O)
  let Uₓ := Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let f := s.toRingedToposHom.toToposHom
  have h_underlying : F ⋙ Uₓ ≅ Uₚ ⋙ f.pushforward := s.pushforwardModulesUnderlyingIso
  have hlim : PreservesFiniteLimits F := by
    have : PreservesFiniteLimits Uₚ :=
      preservesFiniteLimits_moduleSheafFunctor s.point.J
        (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O)
    have : PreservesFiniteLimits f.pushforward := by
      have : PreservesLimits f.pushforward := f.adj.rightAdjoint_preservesLimits
      infer_instance
    have : PreservesFiniteLimits (Uₚ ⋙ f.pushforward) :=
      comp_preservesFiniteLimits Uₚ f.pushforward
    have : PreservesFiniteLimits (F ⋙ Uₓ) :=
      preservesFiniteLimits_of_natIso h_underlying.symm
    have : ReflectsFiniteLimits Uₓ :=
      reflectsFiniteLimits_moduleSheafFunctor X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    exact preservesFiniteLimits_of_reflects_of_preserves F Uₓ
  let V := SheafOfModules.forget.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let G := F ⋙ V
  let T := PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj ⋙
    (whiskeringRight _ _ _).obj (forget AddCommGrpCat.{w})
  have : PreservesFiniteLimits F := hlim
  have : PreservesFiniteLimits V := SheafOfModules.Finite.forgetPreservesFiniteLimits _
  have : V.Full := (SheafOfModules.fullyFaithfulForget _).full
  have : V.Faithful := (SheafOfModules.fullyFaithfulForget _).faithful
  have : PreservesFiniteLimits G := comp_preservesFiniteLimits F V
  have hepi : PreservesEpimorphisms G := by
    have : PreservesEpimorphisms Uₚ :=
      preservesEpimorphisms_moduleSheafFunctor s.point.J
        (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O)
    have : SplitEpiCategory s.point.Topos :=
      s.pointEquiv.inverse.splitEpiCategoryImpOfIsEquivalence
    have : PreservesEpimorphisms (f.pushforward ⋙ sheafToPresheaf X.J (Type w)) :=
      preservesEpimorphisms_of_splitEpiCategory _
    have : PreservesEpimorphisms (Uₚ ⋙ f.pushforward ⋙ sheafToPresheaf X.J (Type w)) :=
      inferInstance
    have hiso : G ⋙ T ≅ Uₚ ⋙ f.pushforward ⋙ sheafToPresheaf X.J (Type w) :=
      Functor.isoWhiskerRight h_underlying (sheafToPresheaf X.J (Type w))
    have : PreservesEpimorphisms (G ⋙ T) := PreservesEpimorphisms.of_iso hiso.symm
    have : T.Faithful := by dsimp [T]; infer_instance
    have : ReflectsEpimorphisms T := Functor.reflectsEpimorphisms_of_faithful T
    exact Functor.preservesEpimorphisms_of_preserves_of_reflects G T
  have : PreservesEpimorphisms G := hepi
  have : PreservesZeroMorphisms G := preservesZeroMorphisms_of_preserves_terminal_object
  have : G.Additive := additive_of_preserves_binary_products G
  have : PreservesHomology G := Functor.preservesHomology_of_preservesEpis_and_kernels G
  have : PreservesFiniteColimits G := Functor.preservesFiniteColimits_of_preservesHomology G
  rw [exactFunctor_iff]
  exact ⟨hlim, preservesFiniteColimits_of_reflects_of_preserves F V⟩

/-- **Stacks 05V8.** The canonical map `p^*p_*M ⟶ M` is a surjection of `O_p`-modules: it is
the counit of the pullback-pushforward adjunction of Stacks 03D7, hence a morphism of sheaves
of modules, and it is an epimorphism because the direct image is faithful. -/
@[stacks 05V8 "surjectivity of the counit"]
theorem pullbackPushforwardModules_counit_epi
    [HasWeakSheafify X.J AddCommGrpCat.{w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify s.point.J AddCommGrpCat.{w}]
    [s.point.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O)) :
    Epi ((pullbackAdjPushforwardModules s.toRingedToposHom).counit.app M) := by
  let adj := pullbackAdjPushforwardModules s.toRingedToposHom
  let Uₚ := Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O)
  let Uₓ := Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  have hp : p.pushforward.Faithful := by
    have : ∀ A : Type w, Epi (p.adj.counit.app A) := fun A => inferInstance
    exact p.adj.faithful_R_of_epi_counit_app
  have : (Uₚ ⋙ s.pointEquiv.functor ⋙ p.pushforward).Faithful := inferInstance
  have : (pushforwardModules s.toRingedToposHom ⋙ Uₓ).Faithful :=
    Functor.Faithful.of_iso s.pushforwardUnderlyingStalkIso.symm
  have hQ : (pushforwardModules s.toRingedToposHom).Faithful :=
    Functor.Faithful.of_comp (pushforwardModules s.toRingedToposHom) Uₓ
  exact @Adjunction.counit_epi_of_R_faithful _ _ _ _ _ _ adj hQ M

/-- **The counit `p^*p_*M ⟶ M` of the adjunction of Stacks 03D7 has, as its underlying map of
sheaves, the counit `p⁻¹p_*M ⟶ M` of the morphism of topoi out of the ringed point.** Both are
the transpose of the identity, and the two transpositions agree: the pullback of modules is the
inverse image of modules followed by extension of scalars along `f♯`, the first contributes the
counit of Stacks 03D3 — which on underlying sheaves is the counit of `f⁻¹ ⊣ f_*`
(`moduleSheafFunctor_map_inverseImageAdjDirectImageModules_counit_app`) — and the second
contributes the counit of a restriction of scalars along an isomorphism, which is the identity
on underlying sheaves. -/
theorem pullbackPushforwardModules_counit_underlying
    [HasWeakSheafify s.point.J AddCommGrpCat.{w}]
    [s.point.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O)).map
        ((pullbackAdjPushforwardModules s.toRingedToposHom).counit.app M) =
      s.pullbackUnderlyingImageIso.hom.app
          ((pushforwardModules s.toRingedToposHom).obj M) ≫
        s.toRingedToposHom.toToposHom.adj.counit.app
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O) M) := by
  have h1 : (pullbackAdjPushforwardModules s.toRingedToposHom).counit.app M =
      s.extendScalarsFSharpIsoRestrictScalars.hom.app
          ((inverseImageModules s.toRingedToposHom.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
            ((pushforwardModules s.toRingedToposHom).obj M)) ≫
        (SheafOfModules.restrictScalars s.ringIso.inv).map
            ((inverseImageAdjDirectImageModules s.toRingedToposHom.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).counit.app
              ((SheafOfModules.restrictScalars
                s.toRingedToposHom.fSharpInverseImage).obj M)) ≫
          s.ringIsoRestrictScalarsAdjunction.counit.app M :=
    comp_counit_app_of_leftAdjointUniq _ _ _ M
  have h2 : (Sheaf.moduleSheafFunctor
        (inverseImageRingSheaf s.toRingedToposHom.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).map
        ((inverseImageAdjDirectImageModules s.toRingedToposHom.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).counit.app
          ((SheafOfModules.restrictScalars s.toRingedToposHom.fSharpInverseImage).obj M)) =
      s.toRingedToposHom.toToposHom.adj.counit.app
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O) M) :=
    moduleSheafFunctor_map_inverseImageAdjDirectImageModules_counit_app _ _ _
  have h3 : (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O)).map
      ((SheafOfModules.restrictScalars s.ringIso.inv).map
          ((inverseImageAdjDirectImageModules s.toRingedToposHom.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).counit.app
            ((SheafOfModules.restrictScalars s.toRingedToposHom.fSharpInverseImage).obj M)) ≫
        s.ringIsoRestrictScalarsAdjunction.counit.app M) =
      s.toRingedToposHom.toToposHom.adj.counit.app
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O) M) := by
    refine ((Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O)).map_comp _ _).trans ?_
    refine (congrArg (fun z => (Sheaf.moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O)).map
      ((SheafOfModules.restrictScalars s.ringIso.inv).map
        ((inverseImageAdjDirectImageModules s.toRingedToposHom.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).counit.app
          ((SheafOfModules.restrictScalars
            s.toRingedToposHom.fSharpInverseImage).obj M))) ≫ z)
      (s.moduleSheafFunctor_map_ringIsoRestrictScalarsAdjunction_counit_app M)).trans ?_
    exact (Category.comp_id _).trans h2
  have h4 := congrArg (fun z => (Sheaf.moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O)).map
      (s.extendScalarsFSharpIsoRestrictScalars.hom.app
        ((inverseImageModules s.toRingedToposHom.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
          ((pushforwardModules s.toRingedToposHom).obj M))) ≫ z) h3
  exact (congrArg (Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O)).map h1).trans
    (((Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O)).map_comp _ _).trans h4)

/-- **The canonical identification `p⁻¹p_*M = (p^*p_*M)^♭`**: the stalk of the underlying sheaf
of the pullback of the direct image of `M` is `p⁻¹p_*` of the stalk of `M`. It is built from the
identification of the underlying sheaf of a pullback with the inverse image of the underlying
sheaf (`pullbackUnderlyingImageIso`), the identification `Sh(pt) = Sets` of the situation
together with its identification of the inverse image with the stalk functor, and the canonical
identification of the direct image along the ringed point with the skyscraper functor of the
point as right adjoints of the stalk functor (`pointPushforwardIso`). -/
def pullbackPushforwardStalkIso
    [HasWeakSheafify s.point.J AddCommGrpCat.{w}]
    [s.point.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O)) :
    s.pointEquiv.functor.obj ((Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O)).obj
        ((s.toRingedToposHom.pullbackModules).obj
          ((pushforwardModules s.toRingedToposHom).obj M))) ≅
      p.inverseImage.obj (p.pushforward.obj (s.pointEquiv.functor.obj
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O)).obj M))) :=
  s.pointEquiv.functor.mapIso
      (s.pullbackUnderlyingImageIso.app ((pushforwardModules s.toRingedToposHom).obj M)) ≪≫
    s.pointEquiv.functor.mapIso (s.toRingedToposHom.toToposHom.inverseImage.mapIso
      (s.toRingedToposHom.toToposHom.pushforward.mapIso
        (s.pointEquiv.unitIso.app
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O) M)))) ≪≫
    s.inverseImageIso.app _ ≪≫
    p.inverseImage.mapIso (s.pointPushforwardIso.app _)

/-- **Stacks 05V8.** The canonical surjection `p⁻¹p_*M ⟶ M` of Stacks 05V7 — the counit of the
adjunction `p⁻¹ ⊣ p_*` of the point — is `O_p`-linear: under the canonical identification
`p⁻¹p_*M = (p^*p_*M)^♭` it is the underlying map of the counit `p^*p_*M ⟶ M` of the adjunction
of Stacks 03D7 for modules, which is a morphism of sheaves of `O_p`-modules by construction.

This is the source's argument: `p⁻¹O = O_p`, hence `p^* = p⁻¹`, hence the map of Stacks 05V7 is
the counit of the adjunction for modules, "whence linear". -/
@[stacks 05V8 "(2) the canonical surjection p⁻¹p_*M → M is O_p-linear"]
theorem pullbackPushforwardModules_counit_stalk
    [HasWeakSheafify s.point.J AddCommGrpCat.{w}]
    [s.point.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O) ⋙
      s.pointEquiv.functor).map
        ((pullbackAdjPushforwardModules s.toRingedToposHom).counit.app M) =
      (s.pullbackPushforwardStalkIso M).hom ≫
        p.adj.counit.app (s.pointEquiv.functor.obj
          ((Sheaf.moduleSheafFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O)).obj M)) := by
  have h1 := equivalence_functor_map_counit_app
    s.toRingedToposHom.toToposHom.adj s.pointEquiv s.inverseImageIso p.adj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf s.point.O) M)
  have h2 := congrArg (fun z => s.pointEquiv.functor.map
      (s.pullbackUnderlyingImageIso.hom.app
        ((pushforwardModules s.toRingedToposHom).obj M)) ≫ z) h1
  exact (congrArg s.pointEquiv.functor.map (s.pullbackPushforwardModules_counit_underlying M)).trans
    ((s.pointEquiv.functor.map_comp _ _).trans (h2.trans (comp_assoc₅ _ _ _ _ _)))

end RingedPointSituation

end Stacks.Sheaves.RingedPoint
