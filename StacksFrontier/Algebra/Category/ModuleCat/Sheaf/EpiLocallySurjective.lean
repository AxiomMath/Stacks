module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# Epimorphisms of sheaves of modules are the locally surjective morphisms

Let `R : Sheaf J RingCat` be a sheaf of rings on a site. A morphism `f : M ⟶ N` of sheaves
of `R`-modules is an epimorphism exactly when the underlying morphism of sheaves of abelian
groups is locally surjective, i.e. when every section of `N` is, after restriction along the
arrows of some covering sieve, in the image of `f`.

## Main definitions

* `counitApp`: the counit `(sheafification (𝟙 R.obj)).obj M.val ⟶ M` of the sheafification
  adjunction for presheaves of modules, at a sheaf of modules `M`.

## Main results

* `isLocallySurjective_of_epi`: an epimorphism of sheaves of modules has locally surjective
  underlying morphism of presheaves of abelian groups.
* `epi_of_isLocallySurjective`: the converse.
* `epi_iff_isLocallySurjective`: the two statements combined.
* `epi_toSheaf_map` and the instance `preservesEpimorphismsToSheaf`: the forgetful functor to
  sheaves of abelian groups preserves epimorphisms.
* `imageSieve_mem_of_epi` and `exists_covering_of_epi`: the section-level form, saying that
  every section of the target is locally in the image.

The results are stated for `SheafOfModules.{t} R` with `R : Sheaf J RingCat.{u}`, the universe
`t` of the module sections being independent of the universe `u` of the ring sections.

## References

* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe v u u' t

namespace Stacks.SheafOfModules.EpiMono

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]

/-- The counit of the sheafification adjunction for presheaves of `R.obj`-modules, evaluated
at a sheaf of modules `M`, as a morphism
`(PresheafOfModules.sheafification (𝟙 R.obj)).obj M.val ⟶ M`. -/
noncomputable def counitApp (M : SheafOfModules.{t} R) :
    (PresheafOfModules.sheafification (J := J) (𝟙 R.obj)).obj M.val ⟶ M :=
  (PresheafOfModules.sheafificationAdjunction (J := J) (𝟙 R.obj)).counit.app M

/-- The counit of the sheafification adjunction for presheaves of modules is an isomorphism:
a sheaf of modules is its own sheafification. -/
instance isIsoCounitApp (M : SheafOfModules.{t} R) : IsIso (counitApp (J := J) M) :=
  NatIso.isIso_app_of_isIso _ M

/-- Naturality of `counitApp`: sheafifying the underlying morphism of presheaves of modules
and then applying the counit is the same as applying the counit and then the morphism. -/
lemma counitApp_naturality {M N : SheafOfModules.{t} R} (f : M ⟶ N) :
    (PresheafOfModules.sheafification (J := J) (𝟙 R.obj)).map f.val ≫ counitApp N =
      counitApp M ≫ f :=
  (PresheafOfModules.sheafificationAdjunction (J := J) (𝟙 R.obj)).counit.naturality f

/-- If `f` is an epimorphism of sheaves of modules, then sheafifying the inclusion of the
image of `f.val` (an image taken in the abelian category of presheaves of modules) gives an
isomorphism of sheaves of modules. -/
lemma isIsoSheafificationMapImageι {M N : SheafOfModules.{t} R} (f : M ⟶ N) [Epi f] :
    IsIso ((PresheafOfModules.sheafification (J := J) (𝟙 R.obj)).map (image.ι f.val)) := by
  have h1 : Epi ((PresheafOfModules.sheafification (J := J) (𝟙 R.obj)).map
      (factorThruImage f.val) ≫
      (PresheafOfModules.sheafification (J := J) (𝟙 R.obj)).map (image.ι f.val) ≫
      counitApp N) := by
    rw [← Category.assoc, ← Functor.map_comp, image.fac, counitApp_naturality]
    exact epi_comp _ _
  have h2 : Epi ((PresheafOfModules.sheafification (J := J) (𝟙 R.obj)).map (image.ι f.val) ≫
      counitApp N) :=
    epi_of_epi ((PresheafOfModules.sheafification (J := J) (𝟙 R.obj)).map
      (factorThruImage f.val)) _
  have h3 : IsIso ((PresheafOfModules.sheafification (J := J) (𝟙 R.obj)).map (image.ι f.val) ≫
      counitApp N) := isIso_of_mono_of_epi _
  exact IsIso.of_isIso_comp_right _ (counitApp N)

/-- An epimorphism of sheaves of modules is locally surjective: the underlying morphism of
presheaves of abelian groups is locally surjective for `J`. -/
theorem isLocallySurjective_of_epi {M N : SheafOfModules.{t} R} (f : M ⟶ N) [Epi f] :
    Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R.obj).map f.val) := by
  have := isIsoSheafificationMapImageι f
  have : IsIso ((presheafToSheaf J AddCommGrpCat.{t}).map
      ((PresheafOfModules.toPresheaf R.obj).map (image.ι f.val))) :=
    inferInstanceAs (IsIso ((SheafOfModules.toSheaf R).map
      ((PresheafOfModules.sheafification (J := J) (𝟙 R.obj)).map (image.ι f.val))))
  have hι : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map (image.ι f.val)) :=
    (Presheaf.isLocallySurjective_presheafToSheaf_map_iff J _).1
      (Sheaf.isLocallySurjective_of_iso _)
  have hπ : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map (factorThruImage f.val)) :=
    Presheaf.isLocallySurjective_of_surjective J _ fun U ↦
      PresheafOfModules.surjective_of_epi (factorThruImage f.val) U
  rw [← image.fac f.val, Functor.map_comp]
  exact Presheaf.isLocallySurjective_comp J _ _

omit [HasSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}] in
/-- A morphism of sheaves of modules whose underlying morphism of presheaves of abelian groups
is locally surjective is an epimorphism. -/
theorem epi_of_isLocallySurjective {M N : SheafOfModules.{t} R} (f : M ⟶ N)
    (hf : Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R.obj).map f.val)) :
    Epi f := by
  have : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map f) := hf
  exact (SheafOfModules.toSheaf R).epi_of_epi_map (Sheaf.epi_of_isLocallySurjective _)

/-- A morphism of sheaves of modules is an epimorphism if and only if the underlying morphism
of presheaves of abelian groups is locally surjective. -/
theorem epi_iff_isLocallySurjective {M N : SheafOfModules.{t} R} (f : M ⟶ N) :
    Epi f ↔ Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R.obj).map f.val) :=
  ⟨fun _ ↦ isLocallySurjective_of_epi f, epi_of_isLocallySurjective f⟩

/-- The forgetful functor from sheaves of `R`-modules to sheaves of abelian groups preserves
epimorphisms. -/
instance preservesEpimorphismsToSheaf :
    (SheafOfModules.toSheaf.{t} (J := J) R).PreservesEpimorphisms where
  preserves f _ := by
    have : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map f) :=
      isLocallySurjective_of_epi f
    exact Sheaf.epi_of_isLocallySurjective _

/-- An epimorphism of sheaves of modules becomes an epimorphism of sheaves of abelian
groups. -/
lemma epi_toSheaf_map {M N : SheafOfModules.{t} R} (f : M ⟶ N) [Epi f] :
    Epi ((SheafOfModules.toSheaf R).map f) :=
  (SheafOfModules.toSheaf R).map_epi f

/-- If `f` is an epimorphism of sheaves of modules, then for every object `V` and every section `s`
of `N` over `V`, the sieve of arrows along which `s` restricts into the image of `f` is a covering
sieve. -/
theorem imageSieve_mem_of_epi {M N : SheafOfModules.{t} R} (f : M ⟶ N) [Epi f] {V : C}
    (s : ToType (((PresheafOfModules.toPresheaf R.obj).obj N.val).obj (op V))) :
    Presheaf.imageSieve ((PresheafOfModules.toPresheaf R.obj).map f.val) s ∈ J V :=
  have := isLocallySurjective_of_epi f
  Presheaf.imageSieve_mem J _ s

/-- If `f` is an epimorphism of sheaves of modules, every section `s` of `N` over `V` has a
covering sieve of `V` along each arrow of which `s` restricts to a section coming from `M`. -/
theorem exists_covering_of_epi {M N : SheafOfModules.{t} R} (f : M ⟶ N) [Epi f] {V : C}
    (s : ToType (((PresheafOfModules.toPresheaf R.obj).obj N.val).obj (op V))) :
    ∃ S : Sieve V, S ∈ J V ∧ ∀ ⦃W : C⦄ (g : W ⟶ V), S g →
      ∃ t : ToType (((PresheafOfModules.toPresheaf R.obj).obj M.val).obj (op W)),
        ((PresheafOfModules.toPresheaf R.obj).map f.val).app (op W) t =
          ((PresheafOfModules.toPresheaf R.obj).obj N.val).map g.op s :=
  ⟨_, imageSieve_mem_of_epi f s, fun _ _ hg ↦ hg⟩

end Stacks.SheafOfModules.EpiMono

end
