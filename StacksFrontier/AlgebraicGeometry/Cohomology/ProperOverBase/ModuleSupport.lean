module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeExtension
public import StacksFrontier.AlgebraicGeometry.Cohomology.ProperOverBase.Functoriality
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteTypeQuotient
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.Topology.Sheaves.Modules.Exactness

/-!
# Proper support under operations on sheaves of modules

For a morphism of schemes locally of finite type, having support proper over the base is
retained by direct sums and by extensions. The image of a morphism out of a finite type module
with proper support, the cokernel of a morphism into such a module, and any quotient of such a
module again have support proper over the base.

## Main results

* `AlgebraicGeometry.isProperOver_biprod_support`: a direct sum.
* `AlgebraicGeometry.isProperOver_extension_support`: a short exact extension.
* `AlgebraicGeometry.isProperOver_image_support` and
  `AlgebraicGeometry.isProperOver_cokernel_support`: the image and the cokernel of a morphism.
* `AlgebraicGeometry.isProperOver_quotient_support`: a quotient.

## Implementation notes

That a sheaf has proper support is expressed as the existence of a closed subset equal to its
stalkwise support whose reduced induced closed subscheme is proper over the base. Phrasing it
this way also records closedness of the output support, which is part of each conclusion. The
quotient result is stated for a single source sheaf, and so applies to either of the two sheaves
of the source lemma.

For direct sums and extensions the proper-support hypotheses already supply closed supports, so
no finite type or quasi-coherence hypothesis is needed. For images, cokernels and quotients only
the module carrying the proper support must be of finite type; again quasi-coherence is not used.

The support behaves as follows under the two half-exactness properties, and these three facts
are what the five results are assembled from: an epimorphism shrinks the support, a
monomorphism grows it, and the support of the middle term of an exact sequence is contained in
the union of the two outer supports. Each is checked on stalks, using that exactness of a short
complex of sheaves of modules is a stalkwise condition
(`AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact`) and that an
epimorphism of sheaves of modules is locally surjective
(`Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi`).

## References

* [Stacks Project, Tag 0CYU](https://stacks.math.columbia.edu/tag/0CYU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Behaviour of the stalkwise support under epimorphisms and monomorphisms -/

/-- An epimorphism of sheaves of modules does not enlarge the support: the stalk maps are
surjective, so a nonzero stalk downstairs comes from a nonzero stalk upstairs. -/
private theorem supp_subset_of_epi {X : Scheme.{u}}
    {M N : SheafOfModules X.ringCatSheaf} (q : M ⟶ N) [Epi q] :
    SheafOfModules.supp N ⊆ SheafOfModules.supp M := by
  rintro x ⟨b, hb⟩
  have hsurj : Function.Surjective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map q.val)) :=
    (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).mp
      (Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi q) x
  obtain ⟨a, ha⟩ := hsurj b
  refine ⟨a, fun ha0 => hb ?_⟩
  rw [← ha, ha0]
  change ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map q.val)) 0 = 0
  exact map_zero _

/-- A monomorphism of sheaves of modules has monomorphic stalk maps. This is the short complex
`0 ⟶ M ⟶ N` read stalkwise, using that exactness of a short complex of sheaves of modules is a
stalkwise condition. -/
private lemma mono_stalkAddCommGroupFunctor_map_of_mono {X : Scheme.{u}}
    {M N : SheafOfModules.{u} X.ringCatSheaf} (i : M ⟶ N) [Mono i] (x : X) :
    Mono ((SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x).map i) := by
  let F := SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x
  let S : ShortComplex (_root_.SheafOfModules.{u} X.ringCatSheaf) :=
    ShortComplex.mk (0 : M ⟶ M) i (by simp)
  have hmap : (S.map F).Exact :=
    (SheafOfModules.exact_iff_stalkShortComplex_exact X.ringCatSheaf S).1
      ((S.exact_iff_mono rfl).2 ‹Mono i›) x
  exact ((S.map F).exact_iff_mono (F.map_zero M M)).1 hmap

/-- A monomorphism of sheaves of modules does not shrink the support. -/
private theorem supp_subset_of_mono {X : Scheme.{u}}
    {M N : SheafOfModules X.ringCatSheaf} (i : M ⟶ N) [Mono i] :
    SheafOfModules.supp M ⊆ SheafOfModules.supp N := by
  rintro x ⟨a, ha⟩
  let q := (SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x).map i
  have hinj : Function.Injective q :=
    (AddCommGrpCat.mono_iff_injective q).mp (mono_stalkAddCommGroupFunctor_map_of_mono i x)
  refine ⟨q.hom a, fun hzero => ha (hinj ?_)⟩
  change (ConcreteCategory.hom q) a = (ConcreteCategory.hom q) 0
  rw [hzero]
  exact (map_zero (AddCommGrpCat.Hom.hom q)).symm

/-- The support of the middle term of an exact short complex is contained in the union of the
supports of the two outer terms. -/
private theorem supp_middle_subset_of_exact {X : Scheme.{u}}
    (E : ShortComplex X.Modules) (hE : E.Exact) :
    SheafOfModules.supp E.X₂ ⊆ SheafOfModules.supp E.X₁ ∪ SheafOfModules.supp E.X₃ := by
  let S : ShortComplex (_root_.SheafOfModules.{u} X.ringCatSheaf) := E
  have hfg : ∀ x : X,
      Function.Exact
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map E.f.val))
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map E.g.val)) := by
    intro x
    have hstalk :=
      (SheafOfModules.exact_iff_stalkShortComplex_exact X.ringCatSheaf S).1 hE x
    have hfunc := (ShortComplex.ab_exact_iff_function_exact _).mp hstalk
    convert hfunc using 1 <;> rfl
  intro x hx
  by_contra hnot
  let P₁ : TopCat.Presheaf Ab.{u} ↑X.toPresheafedSpace := E.X₁.val.presheaf
  let P₃ : TopCat.Presheaf Ab.{u} ↑X.toPresheafedSpace := E.X₃.val.presheaf
  have hF : ∀ a : P₁.stalk x, a = 0 := fun a =>
    Classical.byContradiction fun ha => hnot (.inl ⟨a, ha⟩)
  have hH : ∀ a : P₃.stalk x, a = 0 := fun a =>
    Classical.byContradiction fun ha => hnot (.inr ⟨a, ha⟩)
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := (hfg x a).mp (hH _)
  apply ha
  rw [← hb, hF b]
  exact (AddCommGrpCat.Hom.hom _).map_zero

/-! ### Proper support -/

/-- A module whose support is closed and contained in a closed subset proper over the base has
support proper over the base. -/
private theorem exists_proper_support_of_supp_subset {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (M : X.Modules)
    (Z : Closeds X) (hZ : IsProperOver f Z)
    (hclosed : IsClosed (SheafOfModules.supp M))
    (hsub : SheafOfModules.supp M ⊆ (Z : Set X)) :
    ∃ W : Closeds X, ((W : Set X) = SheafOfModules.supp M ∧ IsProperOver f W) :=
  ⟨⟨SheafOfModules.supp M, hclosed⟩, rfl, isProperOver_of_le f hsub hZ⟩

/-- A quotient of a finite type module with proper support has proper support. -/
private theorem exists_proper_support_of_epi {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] {F Q : X.Modules}
    [F.IsFiniteType] (q : F ⟶ Q) [Epi q]
    (hF : ∃ Z : Closeds X, ((Z : Set X) = SheafOfModules.supp F ∧ IsProperOver f Z)) :
    ∃ Z : Closeds X, ((Z : Set X) = SheafOfModules.supp Q ∧ IsProperOver f Z) := by
  obtain ⟨Z, hZ, hproper⟩ := hF
  have : Q.IsFiniteType := Scheme.Modules.isFiniteType_of_epi q
  exact exists_proper_support_of_supp_subset f Q Z hproper
    (_root_.SheafOfModules.isClosed_supp Q) ((@supp_subset_of_epi X F Q q ‹Epi q›).trans hZ.ge)

/-- The middle term of a short exact sequence whose outer terms have proper support has proper
support. -/
private theorem exists_proper_support_of_shortExact {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (E : ShortComplex X.Modules)
    (hE : E.ShortExact)
    (hF : ∃ Z : Closeds X, ((Z : Set X) = SheafOfModules.supp E.X₁ ∧ IsProperOver f Z))
    (hG : ∃ Z : Closeds X, ((Z : Set X) = SheafOfModules.supp E.X₃ ∧ IsProperOver f Z)) :
    ∃ Z : Closeds X, ((Z : Set X) = SheafOfModules.supp E.X₂ ∧ IsProperOver f Z) := by
  obtain ⟨ZF, hZF, hPF⟩ := hF
  obtain ⟨ZG, hZG, hPG⟩ := hG
  have hEq : SheafOfModules.supp E.X₂ =
      SheafOfModules.supp E.X₁ ∪ SheafOfModules.supp E.X₃ :=
    (supp_middle_subset_of_exact E hE.exact).antisymm
      (Set.union_subset (@supp_subset_of_mono X E.X₁ E.X₂ E.f hE.mono_f)
        (@supp_subset_of_epi X E.X₂ E.X₃ E.g hE.epi_g))
  refine ⟨ZF ⊔ ZG, ?_, isProperOver_sup f ZF ZG hPF hPG⟩
  simp [hEq, ← hZF, ← hZG]

/-- The direct sum of two sheaves with proper support
has proper support. -/
@[stacks 0CYU "sheaf_operations"]
theorem isProperOver_biprod_support {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F G : X.Modules)
    (b : BinaryBicone F G) (hb : b.IsBilimit)
    (hF : ∃ Z : Closeds X, ((Z : Set X) = SheafOfModules.supp F ∧
      IsProperOver f Z))
    (hG : ∃ Z : Closeds X, ((Z : Set X) = SheafOfModules.supp G ∧
      IsProperOver f Z)) :
    ∃ Z : Closeds X, ((Z : Set X) = SheafOfModules.supp b.pt ∧
      IsProperOver f Z) := by
  let E : ShortComplex X.Modules := ShortComplex.mk b.inl b.snd (by simp)
  have hE : E.ShortExact :=
    .mk' (E.exact_of_f_is_kernel (b.isLimitSndKernelFork hb.isLimit))
      (mono_of_isLimit_fork (b.isLimitSndKernelFork hb.isLimit))
      (epi_of_isColimit_cofork (b.isColimitInlCokernelCofork hb.isColimit))
  exact exists_proper_support_of_shortExact f E hE hF hG

/-- A short exact extension of sheaves with proper
support has proper support. -/
@[stacks 0CYU "sheaf_operations"]
theorem isProperOver_extension_support {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (E : ShortComplex X.Modules) (hE : E.ShortExact)
    (hF : ∃ Z : Closeds X, ((Z : Set X) = SheafOfModules.supp E.X₁ ∧
      IsProperOver f Z))
    (hG : ∃ Z : Closeds X, ((Z : Set X) = SheafOfModules.supp E.X₃ ∧
      IsProperOver f Z)) :
    ∃ Z : Closeds X, ((Z : Set X) = SheafOfModules.supp E.X₂ ∧
      IsProperOver f Z) :=
  exists_proper_support_of_shortExact f E hE hF hG

/-- The image of a morphism from a finite type sheaf with proper
support to an arbitrary sheaf of modules has proper support. -/
@[stacks 0CYU "sheaf_operations"]
theorem isProperOver_image_support {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F G : X.Modules)
    [F.IsFiniteType]
    (u : F ⟶ G)
    (hF : ∃ Z : Closeds X, ((Z : Set X) = SheafOfModules.supp F ∧
      IsProperOver f Z)) :
    ∃ Z : Closeds X, ((Z : Set X) = SheafOfModules.supp (Abelian.image u) ∧
      IsProperOver f Z) :=
  @exists_proper_support_of_epi X S f _ F (Abelian.image u) _
    (Abelian.factorThruImage u) inferInstance hF

/-- The cokernel of a morphism from an arbitrary sheaf of modules to a finite type
sheaf with proper support has proper support. -/
@[stacks 0CYU "sheaf_operations"]
theorem isProperOver_cokernel_support {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F G : X.Modules)
    [G.IsFiniteType]
    (u : F ⟶ G)
    (hG : ∃ Z : Closeds X, ((Z : Set X) = SheafOfModules.supp G ∧
      IsProperOver f Z)) :
    ∃ Z : Closeds X, ((Z : Set X) = SheafOfModules.supp (cokernel u) ∧
      IsProperOver f Z) :=
  @exists_proper_support_of_epi X S f _ G (cokernel u) _ (cokernel.π u) inferInstance hG

/-- A quotient of a finite type sheaf with proper
support has proper support. -/
@[stacks 0CYU "sheaf_operations"]
theorem isProperOver_quotient_support {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F Q : X.Modules)
    [F.IsFiniteType]
    (q : F ⟶ Q) [Epi q]
    (hF : ∃ Z : Closeds X, ((Z : Set X) = SheafOfModules.supp F ∧
      IsProperOver f Z)) :
    ∃ Z : Closeds X, ((Z : Set X) = SheafOfModules.supp Q ∧
      IsProperOver f Z) :=
  exists_proper_support_of_epi f q hF

end AlgebraicGeometry

end
