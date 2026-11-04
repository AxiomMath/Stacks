module

public import StacksFrontier.AlgebraicGeometry.Divisors.EtaTildeTorsionFree
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaAffineComparisonNatural
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaDerivedUnconditional
public import StacksFrontier.Homology.Eta.Derived
import StacksCore.Tactic.StacksAttribute

/-!
# The derived Berthelot–Ogus décalage on an affine scheme, compared with the décalage of modules

Let `R` be a commutative ring, write `A = Γ(Spec R, ⊤)`, and let `D ⊆ Spec R` be an effective
Cartier divisor whose ideal sheaf `I` is generated over `Spec R` by a section `g` whose image
`f ∈ A` is a nonzerodivisor — this is the hypothesis `D = V(f)` of [Stacks, Tag 0GTV].  Then the
derived décalage `Lη_f` on `D(A)` of More on Algebra, [Stacks, Tag 0F7R] and the derived
décalage `Lη_I` on `D_QCoh(𝒪_{Spec R})` of [Stacks, Tag 0F8Q] correspond under the equivalence
`D(A) ≌ D_QCoh(𝒪_{Spec R})` of [Stacks, Tag 06Z0]:

`(-)^~ ⋙ Lη_I ≅ Lη_f ⋙ (-)^~`

as a natural isomorphism of functors `D(A) ⥤ D(𝒪_{Spec R})`.  This is the content of the
**second assertion of [Stacks, Tag 0GTV]**; the first — that `Lη_I` sends `D_QCoh(𝒪_X)` into
itself — is `Stacks.Divisors.Eta.derivedCategoryB_isQuasicoherent_obj` of
`StacksFrontier/AlgebraicGeometry/Divisors/EtaDerivedQuasicoherent.lean`, and the two are put
together, at the Stacks hypotheses, in
`StacksFrontier/AlgebraicGeometry/Divisors/EtaDerivedBerthelotOgus.lean`.

## Main definitions

* `Stacks.Eta.DerivedFunctor.etaObjectFunctor`: the chain-level décalage `η_f` as an endofunctor
  of all complexes of `A`-modules.
* `Stacks.Eta.DerivedDescent.moduleDerivedEta`: the derived décalage `Lη_f` on `D(A)`, the
  functor whose existence is [Stacks, Tag 0F7R], together with its comparison
  `Stacks.Eta.DerivedDescent.moduleDerivedEta_iso` with `η_f`.
* `Stacks.Divisors.Eta.tildeGamma`: sheafification `Mod(A) ⥤ Mod(𝒪_{Spec R})`, and
  `Stacks.Divisors.Eta.derivedTildeGamma` its derived functor.
* `Stacks.Divisors.Eta.tildeTorsionFreeComplex`: the complex of sheaves attached to a complex of
  `f`-torsion-free `A`-modules, with its `I`-torsion-freeness.

## Main results

* `Stacks.Divisors.Eta.etaTildeChainIso`: the chain-level comparison `η_I(M̃^•) ≅ (η_f M^•)^~`,
  **as a natural isomorphism of functors** on the complexes of `f`-torsion-free `A`-modules.
* `Stacks.Divisors.Eta.derivedEtaAffineComparison`: the comparison at a generating section `g`
  of `I` with nonzerodivisor image; the second assertion of [Stacks, Tag 0GTV] is read off it in
  `StacksFrontier/AlgebraicGeometry/Divisors/EtaDerivedBerthelotOgus.lean`, where the tag is
  `Stacks.Divisors.Eta.derivedEta_isQuasicoherent_and_affineComparison`.

## Implementation notes

**The ring is `A = Γ(Spec R, ⊤)`, not `R`.** [Stacks, Tag 0GTV] takes `X = Spec(A)` and
`f ∈ A = Γ(X, 𝒪_X)`; here the scheme is presented as `Spec R` and the generating section `g`
lives in `(idealSheaf D)(⊤)`, so its image `f` lives in `Γ(Spec R, ⊤)`.  Taking that ring as
`A` is what makes the comparison available with no transport of the décalage along
`AlgebraicGeometry.Scheme.ΓSpecIso R`: the two rings are canonically isomorphic, and the
isomorphism is absorbed into the sheafification functor rather than applied to `η`.  The
implementation notes of `StacksFrontier/AlgebraicGeometry/Divisors/EtaDerivedQuasicoherent.lean`
previously named such a transport as a missing input; it is not needed at this reading of `A`.
Concretely `Stacks.Divisors.Eta.derivedTildeGamma` is the derived functor of
`Stacks.Divisors.Eta.tildeGamma = ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv ⋙ tilde`,
so it is the derived sheafification of [Stacks, Tag 06Z0] preceded by the derived restriction of
scalars along `Γ(Spec R, ⊤) ≅ R`.  That restriction of scalars is an equivalence of abelian
categories — `Stacks.Divisors.Eta.gammaRestrict` carries the instance — and the full
faithfulness and essential image of the `~` factor are
`AlgebraicGeometry.StandardModel.mapDerivedCategoryFullyFaithful` and
`AlgebraicGeometry.StandardModel.isQuasicoherent_homology_iff_exists_iso_mapDerivedCategory`;
that the *derived* functor of the restriction of scalars is again an equivalence is not recorded
here, and is not used: the content of the second assertion is the natural isomorphism, not the
invertibility of the functor it is transported along.

**`f` is a nonzerodivisor.**  The functor `Lη_f` of [Stacks, Tag 0F7R] exists only for such an
`f` — `Lη_f` is the localization lift along
`Stacks.Eta.DerivedDescent.isLocalization_underlyingComplexCompQ`, whose input is the existence
of flat, hence `f`-torsion-free, resolutions — so the comparison here takes it as the argument
`hfg`.  It is not an extra hypothesis of the tag: for an effective Cartier divisor with
`D.ideal ⊤ = (f)` it is `Stacks.Divisors.Eta.mem_nonZeroDivisors_of_ideal_eq_span` of
`StacksFrontier/AlgebraicGeometry/Divisors/EtaDerivedBerthelotOgus.lean`.

**Two spellings of the chain-level décalage of modules.**  `Stacks.Eta.DerivedFunctor.etaFunctor`
acts on `CochainComplex (FTorsionFreeModule f) ℤ`, where the torsion-freeness is attached to the
terms, while `EtaComplex.etaObject` — the spelling the affine comparison of [Stacks, Tag 0F8M]
produces — acts on all complexes.  The two are not interchangeable: `Functor.mapHomologicalComplex`
maps the differential of a `CochainComplex.of`, and the `dite` in it does not commute with a
functor definitionally.  Rather than compare them, `Stacks.Eta.DerivedFunctor.etaLift` lifts
`etaObjectFunctor` back into the complexes of `f`-torsion-free modules and
`Stacks.Eta.DerivedFunctor.etaLiftEtaFunctor` exhibits that lift as an
`Stacks.Eta.DerivedFunctor.EtaFunctor`, which is the interface
`Stacks.Eta.QuasiIsoPreservation.quasiIso_etaPow_of_quasiIso` — [Stacks, Tag 0F7Q] — asks for.
`Stacks.Eta.DerivedDescent.moduleDerivedEta` is therefore built directly at the spelling the
comparison uses, and no translation between the two is needed anywhere.

**Two spellings of the sheaves of modules.**  `Stacks.IdealTorsion.Eta.etaFunctor` is indexed by
`Stacks.SheafOfModules.Tensor.ringSheaf (Spec R).toRingedSpace.sheaf` while
`AlgebraicGeometry.tilde.functor` lands in
`(Spec R).Modules`; these are the same type but instance search does not cross between them, and
the checks that do cross run only at default transparency.  They are expensive: each one takes
seconds, and a composite that performs several at once exhausts the elaborator.  Every such
check is therefore made once, in a declaration of its own with an explicit statement —
`Stacks.Divisors.Eta.tildeGammaCounitComplex`, `Stacks.Divisors.Eta.etaSectionsIsoTilde`,
`Stacks.Divisors.Eta.isQuasicoherent_sheafEta_tildeTorsionFreeComplex` — and the assembly then
only composes morphisms whose types already agree.  For the same reason the naturality of the
chain-level comparison is proved by `Stacks.Divisors.Eta.naturality_assembly`, a diagram lemma
in an arbitrary pair of categories: all of the unification is then done by `exact`.

**Why the `Mono` argument of the décalage is passed by name.**
`Stacks.IdealTorsion.Eta.etaFunctor` and `Stacks.IdealTorsion.Eta.derivedEta_iso` are indexed by
`Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf`, whereas `Stacks.Divisors.Eta.idealSheaf` and
its inclusion — and so the instance `Stacks.Divisors.Eta.mono_idealSheafι` — are indexed by
`Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩`.
`X.sheaf` is a `def`, so the two agree at default transparency but not at the transparency
instance search runs at, and `Mono (idealSheafι D)` is therefore not synthesized at an
application of either functor although the instance is in scope.  Both are applied with `@`,
with `mono_idealSheafι D` and `isInvertible_idealSheaf D` given by name; the application itself
unifies the two spellings, which it may, being elaborated at default transparency.  No bridging
instance is declared and no name is restored.

**The derived category is the standard model**, which is the one
`Stacks.Divisors.Eta.derivedEtaData` is built at; the attribute is given priority `10000`
because the `HasDerivedCategory` declarations of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` are global instances.

**How the derived statement is assembled.**  Both sides of the conclusion are functors out of
`D(A)`, and `D(A)` is the localization of the complexes of `f`-torsion-free `A`-modules at the
quasi-isomorphisms (`Stacks.Eta.DerivedDescent.isLocalization_underlyingComplexCompQ`), so a
natural isomorphism between them is the same thing as one between their restrictions, by
`CategoryTheory.Localization.liftNatIso`.  The restriction of `(-)^~ ⋙ Lη_I` is identified with
`η_I ⋙ Q` by the comparison of [Stacks, Tag 0F8Q]
(`Stacks.IdealTorsion.Eta.derivedEta_iso`) together with
`CategoryTheory.Functor.mapDerivedCategoryFactors`, and the restriction of `Lη_f ⋙ (-)^~` with
`η_f ⋙ (-)^~ ⋙ Q` by `Stacks.Eta.DerivedDescent.moduleDerivedEta_iso` and the same factorization;
what joins them is `Stacks.Divisors.Eta.etaTildeChainIso`.

## References

* [Stacks Project, Tag 0GTV](https://stacks.math.columbia.edu/tag/0GTV)
* [Stacks Project, Tag 0F8Q](https://stacks.math.columbia.edu/tag/0F8Q)
* [Stacks Project, Tag 0F8M](https://stacks.math.columbia.edu/tag/0F8M)
* [Stacks Project, Tag 0F7R](https://stacks.math.columbia.edu/tag/0F7R)
* [Stacks Project, Tag 0F7Q](https://stacks.math.columbia.edu/tag/0F7Q)
* [Stacks Project, Tag 0GT5](https://stacks.math.columbia.edu/tag/0GT5)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.IdealTorsion (IsIdealTorsionFree GeneratesIdealOn)
open Stacks.IdealTorsion.Eta (etaObj sectionsComplex sectionsFunctor generatorSection)

universe w u

namespace Stacks.Divisors.Eta

variable (R : CommRingCat.{u})

/-- The ring of global functions on `Spec R`. -/
abbrev GammaTop : Type u := ((Spec R).presheaf.obj (op (⊤ : (Spec R).Opens)) : Type u)

/-- Restriction of scalars along `R ≅ Γ(Spec R, ⊤)`. -/
abbrev gammaRestrict : ModuleCat.{u} (GammaTop R) ⥤ ModuleCat.{u} R :=
  ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom

/-- Restriction of scalars along `R ≅ Γ(Spec R, ⊤)` is an equivalence of categories. -/
instance : (gammaRestrict R).IsEquivalence :=
  ModuleCat.restrictScalars_isEquivalence_of_ringEquiv
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv

/-- Sheafification, read on modules over the ring of global functions. -/
abbrev tildeGamma : ModuleCat.{u} (GammaTop R) ⥤ (Spec R).Modules :=
  gammaRestrict R ⋙ AlgebraicGeometry.tilde.functor R

/-- The unit of the `~`–`Γ` adjunction over the ring of global functions. -/
def tildeGammaUnit :
    𝟭 (ModuleCat.{u} (GammaTop R)) ≅
      tildeGamma R ⋙ sectionsFunctor (Spec R).toRingedSpace ⊤ :=
  Functor.fullyFaithfulCancelRight (gammaRestrict R)
    (Functor.leftUnitor _ ≪≫
      Functor.isoWhiskerLeft (gammaRestrict R) AlgebraicGeometry.tilde.toTildeΓNatIso ≪≫
      (Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _).symm)

end Stacks.Divisors.Eta

namespace Stacks.Eta.DerivedFunctor

open Stacks.Eta.DerivedFunctor

/-- Equal morphisms of modules agree at every element.  Stated so that the unification needed
to apply it is carried out by `exact`, at default transparency. -/
theorem hom_apply_of_eq {A : Type u} [CommRing A] {M N : ModuleCat.{u} A} {a b : M ⟶ N}
    (h : a = b) (x : M) : a.hom x = b.hom x := by rw [h]

/-- The décalage as an endofunctor of all cochain complexes of `A`-modules. -/
def etaObjectFunctor {A : Type u} [CommRing A] (f : A) :
    EtaComplex.Complex.{u, u} A ⥤ EtaComplex.Complex.{u, u} A where
  obj C := EtaComplex.etaObject f C
  map g := EtaComplex.etaMap f g
  map_id := EtaComplex.etaMap_id f
  map_comp := EtaComplex.etaMap_comp f

/-- The décalage of a complex of `f`-torsion-free modules, read as an endofunctor of the
complexes of `f`-torsion-free modules: the terms of `η_f C` are `f`-torsion free. -/
def etaLift {A : Type u} [CommRing A] (f : A) :
    CochainComplex (FTorsionFreeModule.{u, u} f) ℤ ⥤
      CochainComplex (FTorsionFreeModule.{u, u} f) ℤ :=
  HomologicalComplex.liftFunctorObjectProperty (isFTorsionFree.{u, u} f)
    (underlyingComplex.{u, u} f ⋙ etaObjectFunctor f)
    (fun _ i => EtaComplex.etaObject_torsionFree f _ i)

/-- Forgetting the torsion-freeness of the terms of `η_f C` returns `η_f` of the underlying
complex. -/
theorem etaLift_comp_underlyingComplex {A : Type u} [CommRing A] (f : A) :
    etaLift.{u} f ⋙ underlyingComplex.{u, u} f =
      underlyingComplex.{u, u} f ⋙ etaObjectFunctor f := rfl

/-- `etaLift` is a décalage functor in the sense of `Stacks.Eta.DerivedFunctor.EtaFunctor`: its
degree-`i` term is the defining submodule of the localization, its differential is the localized
differential and its action on morphisms is the localized map. -/
def etaLiftEtaFunctor {A : Type u} [CommRing A] (f : A) : EtaFunctor.{u, u} f where
  functor := etaLift f
  termIso _ _ := Iso.refl _
  differential M i x :=
    congrArg Subtype.val
      (hom_apply_of_eq (EtaComplex.etaObject_d f ((underlyingComplex.{u, u} f).obj M) i) x)
  map_f _ _ _ := rfl

end Stacks.Eta.DerivedFunctor

namespace Stacks.Eta.DerivedDescent

open Stacks.Eta.DerivedFunctor

variable {A : Type u} [CommRing A]

/-- **The décalage of a quasi-isomorphism of complexes of `f`-torsion-free modules becomes
invertible in `D(A)`**, read at the spelling `EtaComplex.etaObject` of the chain-level
décalage. -/
theorem etaObjectFunctor_inverts [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : A)
    (hf : f ∈ nonZeroDivisors A) :
    (fTorsionFreeQuasiIso.{u, u} f).IsInvertedBy
      (underlyingComplex.{u, u} f ⋙ etaObjectFunctor f ⋙ DerivedCategory.Q) := by
  intro M N a ha
  have hq : QuasiIso ((underlyingComplex.{u, u} f).map a) := ha
  have h : QuasiIso ((etaObjectFunctor f).map ((underlyingComplex.{u, u} f).map a)) :=
    Stacks.Eta.QuasiIsoPreservation.quasiIso_etaPow_of_quasiIso hf (etaLiftEtaFunctor f) a hq
  show IsIso (DerivedCategory.Q.map ((etaObjectFunctor f).map
    ((underlyingComplex.{u, u} f).map a)))
  infer_instance

/-- **The derived décalage `Lη_f` on `D(A)`**, for a nonzerodivisor `f`: the functor whose value
on an object represented by a complex of `f`-torsion-free modules is the class of the chain-level
décalage of that complex.  This is the functor whose existence is
[Stacks, Tag 0F7R], built by the same localization lift and named so that it can be compared
with the sheaf-theoretic décalage. -/
def moduleDerivedEta [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : A)
    (hf : f ∈ nonZeroDivisors A) :
    DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A) :=
  letI := isLocalization_underlyingComplexCompQ.{u, u, w} f hf
  Localization.lift (underlyingComplex.{u, u} f ⋙ etaObjectFunctor f ⋙ DerivedCategory.Q)
    (etaObjectFunctor_inverts f hf) (underlyingComplex.{u, u} f ⋙ DerivedCategory.Q)

/-- **The comparison of `Lη_f` with the chain-level décalage**, on objects and on morphisms. -/
def moduleDerivedEta_iso [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : A)
    (hf : f ∈ nonZeroDivisors A) :
    (underlyingComplex.{u, u} f ⋙ DerivedCategory.Q) ⋙ moduleDerivedEta f hf ≅
      underlyingComplex.{u, u} f ⋙ etaObjectFunctor f ⋙ DerivedCategory.Q :=
  letI := isLocalization_underlyingComplexCompQ.{u, u, w} f hf
  Localization.fac (underlyingComplex.{u, u} f ⋙ etaObjectFunctor f ⋙ DerivedCategory.Q)
    (etaObjectFunctor_inverts f hf) (underlyingComplex.{u, u} f ⋙ DerivedCategory.Q)

end Stacks.Eta.DerivedDescent

namespace Stacks.Divisors.Eta

open Stacks.Eta.DerivedFunctor (isFTorsionFree FTorsionFreeModule underlyingComplex
  etaObjectFunctor etaLift)
open Stacks.IdealTorsion.Eta (torsionFreeProperty TorsionFreeModule torsionFreeComplex)

/-- An `f`-torsion-free module is one on which multiplication by `f` is injective. -/
theorem isSMulRegular_of_isFTorsionFree {A : Type u} [CommRing A] {f : A}
    {N : ModuleCat.{u} A} (h : isFTorsionFree.{u, u} f N) : IsSMulRegular N f := by
  intro x y hxy
  have hsub : f • (x - y) = 0 := by
    rw [smul_sub, show f • x = f • y from hxy, sub_self]
  exact sub_eq_zero.mp (h _ hsub)

variable (R : CommRingCat.{u})

/-- Multiplication by `f ∈ Γ(Spec R, ⊤)` is injective on a module exactly when multiplication by
its image in `R` is injective on the module with scalars restricted along `R ≅ Γ(Spec R, ⊤)`:
the two actions are the same. -/
theorem isSMulRegular_gammaRestrict (N : ModuleCat.{u} (GammaTop R)) {c : GammaTop R}
    (h : IsSMulRegular N c) :
    IsSMulRegular ((gammaRestrict R).obj N) ((Scheme.ΓSpecIso R).hom c) := by
  intro x y hxy
  have hxy' : (Scheme.ΓSpecIso R).inv ((Scheme.ΓSpecIso R).hom c) • (show N from x) =
      (Scheme.ΓSpecIso R).inv ((Scheme.ΓSpecIso R).hom c) • (show N from y) := hxy
  rw [Iso.hom_inv_id_apply] at hxy'
  exact h hxy'

variable (D : (Spec R).IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
  (g : (idealSheaf D).val.obj (op (⊤ : (Spec R).Opens)))

/-- The image in `Γ(Spec R, ⊤)` of a global generator of the ideal sheaf: the element `f` with
`D = V(f)`. -/
abbrev globalGenerator : GammaTop R :=
  Stacks.IdealTorsion.Eta.generatorSection (Spec R).toRingedSpace (idealSheafι D) ⊤ g

/-- **The sheaf complex attached to a complex of `f`-torsion-free modules, with its
`I`-torsion-freeness.** -/
def tildeTorsionFreeComplex :
    CochainComplex (FTorsionFreeModule.{u, u} (globalGenerator R D g)) ℤ ⥤
      CochainComplex (TorsionFreeModule (Spec R).toRingedSpace (idealSheafι D)) ℤ :=
  HomologicalComplex.liftFunctorObjectProperty
    (torsionFreeProperty (Spec R).toRingedSpace (idealSheafι D))
    (underlyingComplex.{u, u} (globalGenerator R D g) ⋙
      (tildeGamma R).mapHomologicalComplex (ComplexShape.up ℤ))
    (fun M n => isIdealTorsionFree_tilde R D _ g
      (isSMulRegular_gammaRestrict R _ (isSMulRegular_of_isFTorsionFree (M.X n).property)))

/-- Forgetting the `I`-torsion-freeness returns the sheaf complex attached to the complex of
modules. -/
theorem tildeTorsionFreeComplex_comp_torsionFreeComplex :
    tildeTorsionFreeComplex R D g ⋙
        torsionFreeComplex (Spec R).toRingedSpace (idealSheafι D) =
      underlyingComplex.{u, u} (globalGenerator R D g) ⋙
        (tildeGamma R).mapHomologicalComplex (ComplexShape.up ℤ) := rfl

/-- Sheafification on complexes of `Γ(Spec R, ⊤)`-modules. -/
abbrev tildeComplexFunctor : CochainComplex (ModuleCat.{u} (GammaTop R)) ℤ ⥤
    CochainComplex (Spec R).Modules ℤ :=
  (tildeGamma R).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Global sections on complexes of `𝒪_{Spec R}`-modules, as complexes of
`Γ(Spec R, ⊤)`-modules. -/
abbrev gammaComplexFunctor : CochainComplex (Spec R).Modules ℤ ⥤
    CochainComplex (ModuleCat.{u} (GammaTop R)) ℤ :=
  (sectionsFunctor (Spec R).toRingedSpace ⊤).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Every term of the sheaf complex attached to a complex of `Γ(Spec R, ⊤)`-modules is
quasi-coherent. -/
theorem isQuasicoherent_tildeGammaComplex
    (C : CochainComplex (ModuleCat.{u} (GammaTop R)) ℤ) (n : ℤ) :
    (((((tildeGamma R).mapHomologicalComplex (ComplexShape.up ℤ)).obj C).X
      n)).IsQuasicoherent :=
  inferInstanceAs
    (((AlgebraicGeometry.tilde.functor R).obj ((gammaRestrict R).obj (C.X n))).IsQuasicoherent)

/-- **A complex of quasi-coherent `𝒪_{Spec R}`-modules is the complex of sheaves attached to its
complex of global sections**, with the complex of global sections read as a complex of
`Γ(Spec R, ⊤)`-modules.  This is `Stacks.Divisors.Eta.gammaTildeComplexIso` at that spelling:
the two are the same term, `AlgebraicGeometry.moduleSpecΓFunctor` being by definition evaluation
at `⊤` followed by restriction of scalars. -/
def tildeGammaCounitComplex (G : CochainComplex (Spec R).Modules ℤ)
    (hqc : ∀ n : ℤ, (G.X n).IsQuasicoherent) :
    (tildeComplexFunctor R).obj ((gammaComplexFunctor R).obj G) ≅ G :=
  gammaTildeComplexIso R G hqc

/-- **The counit of the `~`–`Γ` adjunction is natural on complexes.** -/
theorem tildeGammaCounitComplex_naturality
    {G G' : CochainComplex (Spec R).Modules ℤ}
    (hqc : ∀ n : ℤ, (G.X n).IsQuasicoherent) (hqc' : ∀ n : ℤ, (G'.X n).IsQuasicoherent)
    (x : G ⟶ G') :
    (tildeComplexFunctor R).map ((gammaComplexFunctor R).map x) ≫
        (tildeGammaCounitComplex R G' hqc').hom =
      (tildeGammaCounitComplex R G hqc).hom ≫ x := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  exact (AlgebraicGeometry.Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality (x.f n)

/-- **A complex of `Γ(Spec R, ⊤)`-modules is the complex of global sections of its complex of
sheaves.**  This is the unit of the `~`–`Γ` adjunction over `Γ(Spec R, ⊤)`, read degreewise; the
commutation with the differentials is its naturality. -/
def tildeGammaUnitComplex (C : CochainComplex (ModuleCat.{u} (GammaTop R)) ℤ) :
    C ≅ (gammaComplexFunctor R).obj ((tildeComplexFunctor R).obj C) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (tildeGammaUnit R).app (C.X n))
    (fun i j _ => ((tildeGammaUnit R).hom.naturality (C.d i j)).symm)

/-- The identification of a complex with the global sections of its complex of sheaves is
natural. -/
theorem tildeGammaUnitComplex_naturality
    {C C' : CochainComplex (ModuleCat.{u} (GammaTop R)) ℤ} (b : C ⟶ C') :
    (tildeGammaUnitComplex R C).hom ≫
        (gammaComplexFunctor R).map ((tildeComplexFunctor R).map b) =
      b ≫ (tildeGammaUnitComplex R C').hom :=
  HomologicalComplex.hom_ext _ _ fun n => ((tildeGammaUnit R).hom.naturality (b.f n)).symm

/-- **A diagram lemma.**  The assembly of the three naturality squares that make the affine
comparison of décalages natural in the complex, stated in an arbitrary pair of categories so
that the composition is carried out where nothing needs unfolding. -/
theorem naturality_assembly {B E : Type*} [Category B] [Category E] (T : B ⥤ E)
    {eM eN : E} {pM pN qM qN rM rN : B} (x : eM ⟶ eN) (y : pM ⟶ pN) (z : qM ⟶ qN)
    (w : rM ⟶ rN) (gM : T.obj pM ≅ eM) (gN : T.obj pN ≅ eN) (sM : pM ≅ qM) (sN : pN ≅ qN)
    (vM : qM ≅ rM) (vN : qN ≅ rN)
    (hg : T.map y ≫ gN.hom = gM.hom ≫ x)
    (hs : y ≫ sN.hom = sM.hom ≫ z)
    (hv : z ≫ vN.hom = vM.hom ≫ w) :
    x ≫ gN.inv ≫ T.map (sN.hom ≫ vN.hom) =
      (gM.inv ≫ T.map (sM.hom ≫ vM.hom)) ≫ T.map w := by
  have hx : x ≫ gN.inv = gM.inv ≫ T.map y := (CommSq.horiz_inv ⟨hg.symm⟩).w.symm
  have hinner : y ≫ sN.hom ≫ vN.hom = (sM.hom ≫ vM.hom) ≫ w := by
    rw [← Category.assoc, hs, Category.assoc, hv, ← Category.assoc]
  rw [← Category.assoc, hx, Category.assoc, ← T.map_comp, hinner, T.map_comp,
    Category.assoc]

/-- **A diagram lemma.**  From `uM ≫ p = q ≫ uN` for isomorphisms `uM`, `uN`, the inverses
satisfy `p ≫ uN⁻¹ = uM⁻¹ ≫ q`. -/
theorem comp_inv_eq_inv_comp {C : Type*} [Category C] {W X Y Z : C} (uM : W ≅ X) (uN : Y ≅ Z)
    (p : X ⟶ Z) (q : W ⟶ Y) (h : uM.hom ≫ p = q ≫ uN.hom) :
    p ≫ uN.inv = uM.inv ≫ q := by
  exact (CommSq.horiz_inv ⟨h⟩).w.symm

/-- **A diagram lemma.**  The image under a functor of the square of
`Stacks.Divisors.Eta.comp_inv_eq_inv_comp`, with the two composites already distributed. -/
theorem map_comp_inv_eq_inv_comp {C E : Type*} [Category C] [Category E] (F : C ⥤ E)
    {W X Y Z : C} (uM : W ≅ X) (uN : Y ≅ Z) (p : X ⟶ Z) (q : W ⟶ Y)
    (h : uM.hom ≫ p = q ≫ uN.hom) :
    F.map p ≫ F.map uN.inv = F.map uM.inv ≫ F.map q := by
  rw [← F.map_comp, ← F.map_comp, comp_inv_eq_inv_comp uM uN p q h]

/-- Every term of `η_I(M̃^•)` is quasi-coherent, for a complex `M^•` of `f`-torsion-free
`Γ(Spec R, ⊤)`-modules. -/
theorem isQuasicoherent_sheafEta_tildeTorsionFreeComplex
    (M : CochainComplex (FTorsionFreeModule.{u, u} (globalGenerator R D g)) ℤ) (n : ℤ) :
    (((@Stacks.IdealTorsion.Eta.etaFunctor (Spec R).toRingedSpace (idealSheaf D)
        (idealSheafι D) (mono_idealSheafι D) (isInvertible_idealSheaf D)).obj
        ((tildeTorsionFreeComplex R D g).obj M)).X n).IsQuasicoherent :=
  isQuasicoherent_etaObj D ((torsionFreeComplex (Spec R).toRingedSpace (idealSheafι D)).obj
      ((tildeTorsionFreeComplex R D g).obj M))
    (isQuasicoherent_tildeGammaComplex R
      ((underlyingComplex.{u, u} (globalGenerator R D g)).obj M))
    (Stacks.IdealTorsion.Eta.torsionFreeComplex_torsionFree _ _ _) n

variable (hg : GeneratesIdealOn (Spec R).toRingedSpace ⊤ g)

/-- **[Stacks, Tag 0F8M] at a complex of the shape `M̃^•`:** the complex of global sections of
`η_I(M̃^•)` is `η_f` of the complex of global sections of `M̃^•`. -/
def etaSectionsIsoTilde
    (M : CochainComplex (FTorsionFreeModule.{u, u} (globalGenerator R D g)) ℤ) :
    (gammaComplexFunctor R).obj
        ((@Stacks.IdealTorsion.Eta.etaFunctor (Spec R).toRingedSpace (idealSheaf D)
          (idealSheafι D) (mono_idealSheafι D) (isInvertible_idealSheaf D)).obj
          ((tildeTorsionFreeComplex R D g).obj M)) ≅
      (etaObjectFunctor (globalGenerator R D g)).obj
        ((gammaComplexFunctor R).obj ((tildeComplexFunctor R).obj
          ((underlyingComplex.{u, u} (globalGenerator R D g)).obj M))) :=
  Stacks.IdealTorsion.Eta.etaSectionsIso (Spec R).toRingedSpace (idealSheaf D) (idealSheafι D)
    ((torsionFreeComplex (Spec R).toRingedSpace (idealSheafι D)).obj
      ((tildeTorsionFreeComplex R D g).obj M))
    (Stacks.IdealTorsion.Eta.torsionFreeComplex_torsionFree _ _ _) ⊤ g hg

/-- **The affine comparison of [Stacks, Tag 0F8M] is natural in the complex of modules.** -/
theorem etaSectionsIsoTilde_naturality
    {M N : CochainComplex (FTorsionFreeModule.{u, u} (globalGenerator R D g)) ℤ} (a : M ⟶ N) :
    (gammaComplexFunctor R).map
          ((@Stacks.IdealTorsion.Eta.etaFunctor (Spec R).toRingedSpace (idealSheaf D)
            (idealSheafι D) (mono_idealSheafι D) (isInvertible_idealSheaf D)).map
            ((tildeTorsionFreeComplex R D g).map a)) ≫
        (etaSectionsIsoTilde R D g hg N).hom =
      (etaSectionsIsoTilde R D g hg M).hom ≫
        (etaObjectFunctor (globalGenerator R D g)).map
          ((gammaComplexFunctor R).map ((tildeComplexFunctor R).map
            ((underlyingComplex.{u, u} (globalGenerator R D g)).map a))) :=
  Stacks.IdealTorsion.Eta.etaSectionsIso_naturality _ _ _ _ _ _ _ _ hg

/-- **The chain-level input of the second assertion of [Stacks, Tag 0GTV], at a complex of the
shape `M̃^•`:** `η_I(M̃^•) ≅ (η_f M^•)^~`.  This is the content of
`Stacks.Divisors.Eta.etaObjTildeComplexIso`, assembled again from its two inputs together with
the unit of the `~`–`Γ` adjunction, so that the naturality below has all three to hand. -/
def etaTildeChainIsoApp
    (M : CochainComplex (FTorsionFreeModule.{u, u} (globalGenerator R D g)) ℤ) :
    (@Stacks.IdealTorsion.Eta.etaFunctor (Spec R).toRingedSpace (idealSheaf D)
        (idealSheafι D) (mono_idealSheafι D) (isInvertible_idealSheaf D)).obj
        ((tildeTorsionFreeComplex R D g).obj M) ≅
      (tildeComplexFunctor R).obj ((etaObjectFunctor (globalGenerator R D g)).obj
        ((underlyingComplex.{u, u} (globalGenerator R D g)).obj M)) :=
  (tildeGammaCounitComplex R
      ((@Stacks.IdealTorsion.Eta.etaFunctor (Spec R).toRingedSpace (idealSheaf D)
        (idealSheafι D) (mono_idealSheafι D) (isInvertible_idealSheaf D)).obj
        ((tildeTorsionFreeComplex R D g).obj M))
      (isQuasicoherent_sheafEta_tildeTorsionFreeComplex R D g M)).symm ≪≫
    (tildeComplexFunctor R).mapIso
      (etaSectionsIsoTilde R D g hg M ≪≫
        (etaObjectFunctor (globalGenerator R D g)).mapIso
          (tildeGammaUnitComplex R
            ((underlyingComplex.{u, u} (globalGenerator R D g)).obj M)).symm)

/-- **The chain-level affine comparison of décalages, as a natural isomorphism of functors.**
For a complex `M^•` of `f`-torsion-free `Γ(Spec R, ⊤)`-modules, `η_I(M̃^•) ≅ (η_f M^•)^~`,
naturally in `M^•`.

The three naturality squares composed are: the counit of the `~`–`Γ` adjunction
(`gammaTildeComplexIso_naturality`), the affine comparison of [Stacks, Tag 0F8M]
(`Stacks.IdealTorsion.Eta.etaSectionsIso_naturality`), and the unit of the `~`–`Γ` adjunction
(`tildeGammaUnitComplex_naturality`). -/
def etaTildeChainIso :
    tildeTorsionFreeComplex R D g ⋙
        @Stacks.IdealTorsion.Eta.etaFunctor (Spec R).toRingedSpace (idealSheaf D)
          (idealSheafι D) (mono_idealSheafι D) (isInvertible_idealSheaf D) ≅
      underlyingComplex.{u, u} (globalGenerator R D g) ⋙
        etaObjectFunctor (globalGenerator R D g) ⋙ tildeComplexFunctor R :=
  NatIso.ofComponents (etaTildeChainIsoApp R D g hg) (fun a => by
    refine naturality_assembly (tildeComplexFunctor R) _
      ((gammaComplexFunctor R).map
        ((@Stacks.IdealTorsion.Eta.etaFunctor (Spec R).toRingedSpace (idealSheaf D)
          (idealSheafι D) (mono_idealSheafι D) (isInvertible_idealSheaf D)).map
          ((tildeTorsionFreeComplex R D g).map a)))
      ((etaObjectFunctor (globalGenerator R D g)).map
        ((gammaComplexFunctor R).map ((tildeComplexFunctor R).map
          ((underlyingComplex.{u, u} (globalGenerator R D g)).map a))))
      _ _ _ _ _ _ _ ?_ ?_ ?_
    · exact tildeGammaCounitComplex_naturality R _ _ _
    · exact etaSectionsIsoTilde_naturality R D g hg _
    · exact map_comp_inv_eq_inv_comp (etaObjectFunctor (globalGenerator R D g)) _ _ _ _
        (tildeGammaUnitComplex_naturality R _))

section Derived

attribute [local instance 10000] HasDerivedCategory.standard

open Stacks.Eta.DerivedDescent (moduleDerivedEta moduleDerivedEta_iso
  isLocalization_underlyingComplexCompQ fTorsionFreeQuasiIso)

variable (hfg : globalGenerator R D g ∈ nonZeroDivisors (GammaTop R))

/-- **Derived sheafification on `D(Γ(Spec R, ⊤))`:** the derived functor of `~` — the
equivalence `D(R) ≌ D_QCoh(𝒪_{Spec R})` of [Stacks, Tag 06Z0] — preceded by the derived
restriction of scalars along `Γ(Spec R, ⊤) ≅ R`.  Restriction of scalars along a ring
isomorphism is an equivalence of abelian categories, and `Stacks.Divisors.Eta.gammaRestrict`
carries that instance; that its derived functor is again an equivalence is not recorded here
and is not used below. -/
abbrev derivedTildeGamma : DerivedCategory (ModuleCat.{u} (GammaTop R)) ⥤
    DerivedCategory (Spec R).Modules :=
  (gammaRestrict R).mapDerivedCategory ⋙ (AlgebraicGeometry.tilde.functor R).mapDerivedCategory

/-- Derived sheafification on `D(Γ(Spec R, ⊤))` is computed by the degreewise sheafification of
complexes. -/
def derivedTildeGammaFactors :
    DerivedCategory.Q ⋙ derivedTildeGamma R ≅ tildeComplexFunctor R ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerRight ((gammaRestrict R).mapDerivedCategoryFactors)
      ((AlgebraicGeometry.tilde.functor R).mapDerivedCategory) ≪≫
    Functor.isoWhiskerLeft ((gammaRestrict R).mapHomologicalComplex (ComplexShape.up ℤ))
      ((AlgebraicGeometry.tilde.functor R).mapDerivedCategoryFactors)

/-- `Lη_I` on an object of the shape `M̃^•` is the class of `η_I(M̃^•)`: the comparison of
[Stacks, Tag 0F8Q] restricted along the sheafification of complexes of `f`-torsion-free
modules. -/
def derivedEtaTildeFactors :
    (underlyingComplex.{u, u} (globalGenerator R D g) ⋙ DerivedCategory.Q) ⋙
        (derivedTildeGamma R ⋙ (derivedEtaData D).functor) ≅
      tildeTorsionFreeComplex R D g ⋙
        @Stacks.IdealTorsion.Eta.etaFunctor (Spec R).toRingedSpace (idealSheaf D)
          (idealSheafι D) (mono_idealSheafι D) (isInvertible_idealSheaf D) ⋙
            DerivedCategory.Q :=
  Functor.isoWhiskerLeft (underlyingComplex.{u, u} (globalGenerator R D g))
      (Functor.isoWhiskerRight (derivedTildeGammaFactors R)
        (derivedEtaData D).functor) ≪≫
    Functor.isoWhiskerLeft (tildeTorsionFreeComplex R D g)
      (@Stacks.IdealTorsion.Eta.derivedEta_iso (Spec R).toRingedSpace (idealSheaf D)
        (idealSheafι D) (mono_idealSheafι D) (isInvertible_idealSheaf D)
        (hasTorsionFreeResolutions D))

/-- `Lη_f` on an object of the shape `M^•` is the class of `η_f(M^•)`, sheafified. -/
def derivedEtaModuleTildeFactors :
    (underlyingComplex.{u, u} (globalGenerator R D g) ⋙ DerivedCategory.Q) ⋙
        (moduleDerivedEta (globalGenerator R D g) hfg ⋙ derivedTildeGamma R) ≅
      underlyingComplex.{u, u} (globalGenerator R D g) ⋙
        etaObjectFunctor (globalGenerator R D g) ⋙ tildeComplexFunctor R ⋙
          DerivedCategory.Q :=
  Functor.isoWhiskerRight (moduleDerivedEta_iso (globalGenerator R D g) hfg)
      (derivedTildeGamma R) ≪≫
    Functor.isoWhiskerLeft (underlyingComplex.{u, u} (globalGenerator R D g) ⋙
      etaObjectFunctor (globalGenerator R D g)) (derivedTildeGammaFactors R)

/-- **The derived décalages on an affine scheme correspond, for a generating section.**  Let `R`
be a ring, let `D ⊆ Spec R` be an effective Cartier divisor whose ideal sheaf `I` is generated
over `Spec R` by a section `g`, and let `f ∈ A = Γ(Spec R, ⊤)` be its image, assumed here to be
a nonzerodivisor (`hfg`).  The second assertion of [Stacks, Tag 0GTV], with `D = V(f)` read as
the equation `D.ideal ⊤ = (f)` and the nonzerodivisor property proved rather than assumed, is
`Stacks.Divisors.Eta.derivedEtaAffineComparisonOfIdealEqSpan`, which is this isomorphism at a
generating section produced from `f`.
Then the derived décalage `Lη_f` on `D(A)` and the derived décalage `Lη_I` on
`D_QCoh(𝒪_{Spec R})` correspond under the equivalence of [Stacks, Tag 06Z0]:

`(-)^~ ⋙ Lη_I ≅ Lη_f ⋙ (-)^~`

as functors `D(A) ⥤ D(𝒪_{Spec R})`, where `(-)^~` is derived sheafification.

Both functors on `D(A)` are determined by their restrictions along the complexes of
`f`-torsion-free `A`-modules, which is a localization by [Stacks, Tag 0F7R]'s localization
input, and so is a natural isomorphism between them; the restriction is the chain-level
comparison `Stacks.Divisors.Eta.etaTildeChainIso`. -/
def derivedEtaAffineComparison :
    derivedTildeGamma R ⋙ (derivedEtaData D).functor ≅
      moduleDerivedEta (globalGenerator R D g) hfg ⋙ derivedTildeGamma R :=
  letI := isLocalization_underlyingComplexCompQ (globalGenerator R D g) hfg
  Localization.liftNatIso
    (underlyingComplex.{u, u} (globalGenerator R D g) ⋙ DerivedCategory.Q)
    (fTorsionFreeQuasiIso.{u, u} (globalGenerator R D g))
    (tildeTorsionFreeComplex R D g ⋙
      @Stacks.IdealTorsion.Eta.etaFunctor (Spec R).toRingedSpace (idealSheaf D)
        (idealSheafι D) (mono_idealSheafι D) (isInvertible_idealSheaf D) ⋙
          DerivedCategory.Q)
    (underlyingComplex.{u, u} (globalGenerator R D g) ⋙
      etaObjectFunctor (globalGenerator R D g) ⋙ tildeComplexFunctor R ⋙ DerivedCategory.Q)
    (derivedTildeGamma R ⋙ (derivedEtaData D).functor)
    (moduleDerivedEta (globalGenerator R D g) hfg ⋙ derivedTildeGamma R)
    (h₁ := ⟨derivedEtaTildeFactors R D g⟩)
    (h₂ := ⟨derivedEtaModuleTildeFactors R D g hfg⟩)
    (Functor.isoWhiskerRight (etaTildeChainIso R D g hg) DerivedCategory.Q)

end Derived

end Stacks.Divisors.Eta

end
