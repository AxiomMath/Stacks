module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerived
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomVariance
public import StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.InternalHomComplexQuasiIso
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.RealizationComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexFunctoriality

/-!
# The internal Hom complex along a closed quotient morphism of ringed spaces

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces, so that pushforward
`i_* : Mod(𝒪_Z) ⥤ Mod(𝒪_X)` is left adjoint to sheaf Hom with exact support
`ℰom(𝒪_Z, -) : Mod(𝒪_X) ⥤ Mod(𝒪_Z)`, and let `M` be a cochain complex of `𝒪_Z`-modules and
`I` a cochain complex of `𝒪_X`-modules.  From the underived identification
`SheafHom_X(i_*N, F) ≅ i_* SheafHom_Z(N, ℰom(𝒪_Z, F))`, natural in the `𝒪_Z`-module `N` and in
the `𝒪_X`-module `F`, this file shows that the complex

`i_*(SheafHom^•_Z(M, ℰom^•(𝒪_Z, I)))`

*realizes* the internal Hom complex `SheafHom^•_X(i_*M, I)` in the sense of
`Stacks.SheafOfModules.SheafHomComplex`: its sections over an open `U ⊆ X` are the Hom complex
of the restrictions `(i_*M)|_U ⟶ I|_U`, compatibly with further restriction and with the action
of `𝒪_X(U)`.

The identification of sections is the one of the source.  Sections over `U` of the pushforward
are sections over `i^{-1}U` of `SheafHom^•_Z(M, ℰom^•(𝒪_Z, I))`, hence — by the defining
property of a realization on `Z` — cochains `M|_{i^{-1}U} ⟶ ℰom^•(𝒪_Z, I)|_{i^{-1}U}`.  A
component of such a cochain is a section over `i^{-1}U` of the internal Hom
`Hom_{𝒪_Z}(M^p, ℰom(𝒪_Z, I^q))`, because a section of an internal Hom over an open literally
*is* a morphism of the restrictions to the slice site over that open.  Pushing forward is
restriction to the preimage, so the underived identification turns that section into a section
over `U` of `Hom_{𝒪_X}(i_*M^p, I^q)`, that is, into a component of a cochain
`(i_*M)|_U ⟶ I|_U`.  Compatibility with the differentials is naturality of the underived
identification in its two variables; compatibility with restriction and with scalars is
naturality and linearity of the identification on sections.

## Main definitions

* `Stacks.SheafOfModules.InternalHom.internalHomPrecomp`: precomposition in the first variable
  of the internal Hom of sheaves of modules.
* `RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.PushforwardInternalHom`: the
  underived identification `SheafHom_X(i_*N, -) ≅ i_* SheafHom_Z(N, ℰom(𝒪_Z, -))` of
  [Stacks, Tag 0E2I], bundled with its naturality in `N`.
* `PushforwardInternalHom.sliceEquiv`: the induced additive bijection between morphisms
  `(i_*N)|_U ⟶ F|_U` on `X` and morphisms `N|_{i^{-1}U} ⟶ ℰom(𝒪_Z, F)|_{i^{-1}U}` on `Z`.
* `PushforwardInternalHom.cochainEquiv`: the resulting additive bijection on cochains of a
  fixed degree.
* `Stacks.SheafOfModules.SheafHomComplexComparison`: a canonical isomorphism between any two
  realizations of the internal Hom complex, compatible with their sections.
* `Stacks.SheafOfModules.sheafHomComplexComparison`: that comparison, as the canonical
  isomorphism of two realizations of the internal Hom complex.
* `ClosedQuotientMorphismOfRingedSpaces.pushforwardSheafHomRealization`: the complex
  `i_*(SheafHom^•_Z(M, ℰom^•(𝒪_Z, I)))`, as a realization of the internal Hom complex
  `SheafHom^•_X(i_*M, I)`.
* `RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.pushforwardSheafHomComplexIso`:
  the resulting isomorphism with the canonical internal Hom complex `SheafHom^•_X(i_*M, I)`.

## Main results

* `PushforwardInternalHom.natural_inv`: the inverse of the underived identification is natural
  in the contravariant variable as well.
* `PushforwardInternalHom.cochainEquiv_δ`: the bijection on cochains commutes with the
  differential of the Hom complex, which is what makes the identification of sections an
  isomorphism of complexes.
* `Stacks.SheafOfModules.SheafHomComplex.hom_ext_sections`: a morphism between realizations of
  the internal Hom complex is determined by the map it induces on cochains of sections.
* `Stacks.SheafOfModules.SheafHomComplex.eq_of_isInducedMap`: two morphisms of realizations
  induced by the same pair of morphisms of complexes are equal.
* `ClosedQuotientMorphismOfRingedSpaces.pushforwardSheafHomComplexIso_sections`: the comparison
  with the canonical internal Hom complex matches the two identifications of sections, which is
  what pins it down.
* `ClosedQuotientMorphismOfRingedSpaces.pushforwardSheafHomComplexIso_sections_v`: the
  component at `(p, q)` of the cochain the canonical internal Hom complex attaches to the image
  of a section under the comparison.
* `Stacks.SheafOfModules.sheafHomComplexMap_eq_homMap`: the canonical map of internal Hom
  complexes on a ringed space is the site-level induced map
  `AlgebraicGeometry.RingedSite.homMap`, both being pinned by the same formula on sections.
* `ClosedQuotientMorphismOfRingedSpaces.pushforwardSheafHomComplexIso_natural_right` and
  `pushforwardSheafHomComplexIso_natural_right_homMap`: the comparison is natural in the
  complex `I` of `𝒪_X`-modules, in the two spellings of the induced map.
* `ClosedQuotientMorphismOfRingedSpaces.pushforwardSheafHomComplexIso_natural_left` and
  `pushforwardSheafHomComplexIso_natural_left_homMap`: the comparison is natural in the complex
  `M` of `𝒪_Z`-modules as well, in the same two spellings.  The naturality in `I` is what
  extends the derived identification along a K-injective resolution of the target; this one is
  what a statement about the derived identification at a *fixed* object of `D(𝒪_Z)` needs, that
  identification being built at a chosen cochain representative of the object.  It is consumed
  by `…pushforwardSheafHomComplex_natural_left` and so by
  `…derivedSheafHomPushforwardNatIso_app_cochain`, which is what removes the chosen
  representative from the component formula for the derived identification.

## Implementation notes

The underived identification is a parameter of the constructions below rather than something
they build: it is a statement about the adjoint pair `(i_*, ℰom(𝒪_Z, -))` and the two internal
Homs, with no reference to complexes, and the complex-level statement below is a formal
consequence of it.  It is constructed in
`StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportPushforwardInternalHom`,
whose argument is about adjunctions alone.  It is bundled as a structure because the isomorphism
alone does not determine the construction: naturality in the contravariant variable, which is
not part of the data of a family of isomorphisms of functors, is exactly what makes the
identification compatible with the differential of the source complex.

The right-hand side of the underived identification is written
`(ℰom(𝒪_Z, -) ⋙ SheafHom_{𝒪_Z}(N, -)) ⋙ i_*`, with explicit parentheses, as the construction
of the isomorphism produces it.  The other association is the same functor by
`CategoryTheory.Functor.assoc`, which holds by `rfl`, but declaring it costs a definitional
unfolding of `Functor.comp` inside every field of an `Iso` of functors, which exhausts the
kernel's budget at these universes.  For the same reason the two section-level lemmas
`PushforwardInternalHom.inv_app_app_restrict` and `inv_app_app_smul` are stated with that
composite fully applied, so that no `⋙` occurs in their types.

A realization of the internal Hom complex is determined up to canonical isomorphism by its
identification of sections, since a morphism of sheaves of modules is determined by what it
does to sections; the comparison of two realizations is the composite of one identification
with the inverse of the other, and both of its naturality statements are read off from the
section formula of the induced maps.

Several definitions of the underlying libraries are made locally `implicit_reducible`.  Both
sides of every identification below are spelled over different but definitionally equal sheaves
of rings — the structure sheaf of `X` appears as `structureSheafRing S.X` in the pushforward and as
`structureSheaf S.X.sheaf` in the internal Hom complex, and the restriction of a sheaf of
modules to the opens contained in `U` appears both as `SheafOfModules.overFunctor` and as the
presheaf-level `restrFun` — and these agree only after the forgetting of commutativity is
commuted past a pushforward, which is invisible at the transparency elaboration uses by default.
`AlgebraicGeometry.SheafedSpace.sheaf` is made locally `instance_reducible` for the same reason:
`structureSheafRing S.X` reduces to `S.X.presheaf ⋙ forget₂ _ _`, while `structureSheaf S.X.sheaf`
reaches that presheaf only through that projection.

## References

* [Stacks Project, Tag 0E2I](https://stacks.math.columbia.edu/tag/0E2I)
* [Stacks Project, Tag 0A8S](https://stacks.math.columbia.edu/tag/0A8S)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open CochainComplex CochainComplex.HomComplex

universe u

attribute [local implicit_reducible]
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
  PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj
  PresheafOfModules.presheaf
  PresheafOfModules.toPresheaf
  PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
  SheafOfModules.pushforward
  SheafOfModules.overFunctor
  SheafOfModules.toSheaf
  SheafOfModules.forget
  TopCat.Sheaf
  structureSheafRing
  RingedSpaceModuleAdjunction.modulePushforward
  _root_.internalHom
  _root_.internalHomObj
  _root_.restrFun
  _root_.ORestr
  Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor

attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf

namespace Stacks.PresheafOfModules.InternalHom

/-- Restricting a section of the internal Hom presheaf along `f : V ⟶ U` restricts the local
morphism that section is: its component at an object `W ⟶ V` of the slice site over `V` is the
component of the original at the composite `W ⟶ U`. -/
theorem internalHom_map_app_apply {C : Type u} [Category.{u} C] (O : Cᵒᵖ ⥤ CommRingCat.{u})
    (F G : _root_.PresheafOfModules.{u} (_root_.Oforget O)) {V U : C} (f : V ⟶ U)
    (α : (_root_.restrFun O U).obj F ⟶ (_root_.restrFun O U).obj G) (W : Over V)
    (y : ((_root_.restrFun O V).obj F).obj (op W)) :
    _root_.PresheafOfModules.Hom.app ((_root_.internalHom O F G).map f.op α) (op W) y =
      _root_.PresheafOfModules.Hom.app α (op (Over.mk (W.hom ≫ f))) y :=
  rfl

end Stacks.PresheafOfModules.InternalHom

namespace Stacks.SheafOfModules.InternalHom

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] (O : Sheaf J CommRingCat.{u})

/-- Precomposition in the first variable of the internal Hom of sheaves of modules: a morphism
`f : F ⟶ F'` induces `Hom_O(F', G) ⟶ Hom_O(F, G)`, which on sections over an object `U` is
precomposition with the restriction of `f` to the slice site over `U`. -/
def internalHomPrecomp {F F' : _root_.SheafOfModules.{u} (Tensor.ringSheaf O)} (f : F ⟶ F')
    (G : _root_.SheafOfModules.{u} (Tensor.ringSheaf O)) :
    (internalHomSecondFunctor.{u, u, u, u} J O F').obj G ⟶
      (internalHomSecondFunctor.{u, u, u, u} J O F).obj G :=
  ⟨Stacks.PresheafOfModules.InternalHom.internalHomMapLeft O.obj f.val⟩

/-- On sections over `U`, precomposition in the first variable of the internal Hom is
precomposition with the restriction of the inducing morphism. -/
theorem internalHomPrecomp_val_app
    {F F' : _root_.SheafOfModules.{u} (Tensor.ringSheaf O)} (f : F ⟶ F')
    (G : _root_.SheafOfModules.{u} (Tensor.ringSheaf O)) (U : C)
    (α : (_root_.restrFun O.obj U).obj F'.val ⟶
      (_root_.restrFun O.obj U).obj G.val) :
    ((internalHomPrecomp J O f G).val.app (op U)).hom α =
      (_root_.restrFun O.obj U).map f.val ≫ α :=
  rfl

/-- On sections over `U`, the covariant action of the internal Hom in its second variable is
postcomposition with the restriction of the inducing morphism. -/
theorem internalHomSecondFunctor_map_val_app
    (F : _root_.SheafOfModules.{u} (Tensor.ringSheaf O))
    {G G' : _root_.SheafOfModules.{u} (Tensor.ringSheaf O)} (g : G ⟶ G') (U : C)
    (α : (_root_.restrFun O.obj U).obj F.val ⟶
      (_root_.restrFun O.obj U).obj G.val) :
    (((internalHomSecondFunctor.{u, u, u, u} J O F).map g).val.app (op U)).hom α =
      α ≫ (_root_.restrFun O.obj U).map g.val :=
  rfl

end Stacks.SheafOfModules.InternalHom

namespace Stacks.SheafOfModules

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)

/-- A comparison of realizations of the internal Hom complex: a canonical isomorphism between
any two realizations of `SheafHom^•(K, I)`, compatible with their identifications of sections.
The compatibility pins the isomorphism down, a realization being determined by its sections. -/
structure SheafHomComplexComparison where
  /-- The isomorphism between the underlying complexes of two realizations. -/
  iso : ∀ (K I : CochainComplex (StructureSheafModules Rc) ℤ)
    (H H' : SheafHomComplex Rc K I), H.obj ≅ H'.obj
  /-- On sections over any open, the isomorphism matches the two identifications of sections
  with the Hom complex of the restrictions. -/
  sectionsIso_hom : ∀ (K I : CochainComplex (StructureSheafModules Rc) ℤ)
    (H H' : SheafHomComplex Rc K I) (U : Opens X) (n : ℤ)
    (s : (H.obj.X n).val.obj (op U)),
    AddCommGrpCat.Hom.hom ((H'.sectionsIso U).hom.f n)
        (((iso K I H H').hom.f n).val.app (op U) s) =
      AddCommGrpCat.Hom.hom ((H.sectionsIso U).hom.f n) s

/-- Two morphisms between realizations of the internal Hom complex which induce the same map on
the cochains of sections over every open, in every degree, are equal: a morphism of sheaves of
modules is determined by its sections. -/
theorem SheafHomComplex.hom_ext_sections
    {K I K' I' : CochainComplex (StructureSheafModules Rc) ℤ}
    (H : SheafHomComplex Rc K I) (H' : SheafHomComplex Rc K' I') (a b : H.obj ⟶ H'.obj)
    (hab : ∀ (U : Opens X) (n : ℤ) (s : (H.obj.X n).val.obj (op U)),
      AddCommGrpCat.Hom.hom ((H'.sectionsIso U).hom.f n) ((a.f n).val.app (op U) s) =
        AddCommGrpCat.Hom.hom ((H'.sectionsIso U).hom.f n) ((b.f n).val.app (op U) s)) :
    a = b := by
  refine HomologicalComplex.hom_ext a b fun n => ?_
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  have hid : ∀ y, AddCommGrpCat.Hom.hom ((H'.sectionsIso U.unop).inv.f n)
      (AddCommGrpCat.Hom.hom ((H'.sectionsIso U.unop).hom.f n) y) = y := fun y =>
    congrArg (fun t : _ ⟶ _ => AddCommGrpCat.Hom.hom t y)
      (congrArg (fun φ : _ ⟶ _ => HomologicalComplex.Hom.f φ n)
        (H'.sectionsIso U.unop).hom_inv_id)
  exact (hid _).symm.trans ((congrArg
    (fun y => AddCommGrpCat.Hom.hom ((H'.sectionsIso U.unop).inv.f n) y)
      (hab U.unop n s)).trans (hid _))

/-- Two morphisms between realizations of the internal Hom complex which are both induced by
the same pair of morphisms of complexes are equal: the section formula `z ↦ g ≫ z ≫ f`
determines the morphism. -/
theorem SheafHomComplex.eq_of_isInducedMap
    {K K' I I' : CochainComplex (StructureSheafModules Rc) ℤ} (g : K' ⟶ K) (f : I' ⟶ I)
    (H : SheafHomComplex Rc K I') (H' : SheafHomComplex Rc K' I) {a b : H.obj ⟶ H'.obj}
    (ha : SheafHomComplex.IsInducedMap Rc g f H H' a)
    (hb : SheafHomComplex.IsInducedMap Rc g f H H' b) : a = b :=
  SheafHomComplex.hom_ext_sections Rc H H' a b fun U n s =>
    Cochain.ext _ _ fun p q hpq => (ha U n p q hpq s).trans (hb U n p q hpq s).symm

/-- **The canonical comparison of realizations of the internal Hom complex.**  Two realizations
of `SheafHom^•(K, I)` are isomorphic by the composite of the identification of sections of the
one with the inverse of the identification of sections of the other; the two realizations have
the same Hom complexes of restrictions as targets, so nothing further is involved. -/
def sheafHomComplexComparison : SheafHomComplexComparison Rc where
  iso _ _ H H' := isoOfRealizations Rc H H'
  sectionsIso_hom _ _ H H' U n s := isoOfRealizations_sectionsIso Rc H H' U n s

/-- **The canonical map of internal Hom complexes is the site-level induced map.**  The map
induced on the canonical internal Hom complexes of a ringed space by precomposition with `g`
and postcomposition with `f` is `AlgebraicGeometry.RingedSite.homMap` of the ringed site: both
send a cochain of sections to `g ≫ z ≫ f`, and that formula determines the morphism. -/
theorem sheafHomComplexMap_eq_homMap
    {K K' I I' : CochainComplex (StructureSheafModules Rc) ℤ} (g : K' ⟶ K) (f : I' ⟶ I) :
    sheafHomComplexMap Rc g f =
      AlgebraicGeometry.RingedSite.homMap (ringedSite Rc) g f :=
  SheafHomComplex.eq_of_isInducedMap Rc g f (sheafHomComplex Rc K I') (sheafHomComplex Rc K' I)
    (sheafHomComplexMap_isInduced Rc g f) fun U n p q hpq s =>
      AlgebraicGeometry.RingedSite.sectionsIso_homMap_v (ringedSite Rc) g f U n p q hpq s

end Stacks.SheafOfModules

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

open Stacks.SheafOfModules Stacks.SheafOfModules.InternalHom

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-- The preimage in `Z` of an open subset of `X` along a closed quotient morphism.  Sections of
a pushforward over `U` are sections over this open. -/
abbrev openPreimage (U : Opens S.X) : Opens S.Z := (opensMap S.i).obj U

/-- Taking preimages along `i` preserves inclusions of opens. -/
theorem openPreimage_le_openPreimage {U V : Opens S.X} (hVU : V ≤ U) :
    S.openPreimage V ≤ S.openPreimage U :=
  leOfHom ((opensMap S.i).map (homOfLE hVU))

/-- **Stacks 0E2I, underived form.** The internal Hom out of a pushforward along a closed
quotient morphism of ringed spaces: the natural identification
`Hom_{𝒪_X}(i_*N, -) ≅ i_* Hom_{𝒪_Z}(N, ℰom(𝒪_Z, -))`, together with its naturality in the
`𝒪_Z`-module `N`. -/
structure PushforwardInternalHom where
  /-- The identification of `Hom_{𝒪_X}(i_*N, -)` with `i_* Hom_{𝒪_Z}(N, ℰom(𝒪_Z, -))`, as an
  isomorphism of functors on `𝒪_X`-modules. -/
  iso : ∀ N : SheafOfModules.{u} (structureSheafRing S.Z),
    internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology S.X.carrier) S.X.sheaf
        ((modulePushforward S.i).obj N) ≅
      (S.sheafHomExactSupport ⋙
          internalHomSecondFunctor.{u, u, u, u} (Opens.grothendieckTopology S.Z.carrier)
            S.Z.sheaf N) ⋙ modulePushforward S.i
  /-- The identification is natural in the contravariant variable: precomposing with `i_*g` on
  the left corresponds to precomposing with `g` on the right. -/
  natural : ∀ {N N' : SheafOfModules.{u} (structureSheafRing S.Z)} (g : N ⟶ N')
      (F : SheafOfModules.{u} (structureSheafRing S.X)),
    internalHomPrecomp (Opens.grothendieckTopology S.X.carrier) S.X.sheaf
        ((modulePushforward S.i).map g) F ≫ (iso N).hom.app F =
      (iso N').hom.app F ≫ (modulePushforward S.i).map
        (internalHomPrecomp (Opens.grothendieckTopology S.Z.carrier) S.Z.sheaf g
          (S.sheafHomExactSupport.obj F))

namespace PushforwardInternalHom

variable {S}

/-- The inverse of the underived identification is natural in the contravariant variable. -/
theorem natural_inv (h : S.PushforwardInternalHom)
    {N N' : SheafOfModules.{u} (structureSheafRing S.Z)} (g : N ⟶ N')
    (F : SheafOfModules.{u} (structureSheafRing S.X)) :
    (h.iso N').inv.app F ≫ internalHomPrecomp (Opens.grothendieckTopology S.X.carrier)
          S.X.sheaf ((modulePushforward S.i).map g) F =
      (modulePushforward S.i).map
          (internalHomPrecomp (Opens.grothendieckTopology S.Z.carrier) S.Z.sheaf g
            (S.sheafHomExactSupport.obj F)) ≫ (h.iso N).inv.app F :=
  ((h.iso N').app F).inv_comp_eq.mpr
    (((Iso.eq_comp_inv ((h.iso N).app F)).mpr (h.natural g F)).trans (Category.assoc _ _ _))

/-- The underived identification, read on sections over an open `U ⊆ X`: a morphism
`(i_*N)|_U ⟶ F|_U` of `𝒪_X`-modules on the opens contained in `U` is the same thing as a
morphism `N|_{i^{-1}U} ⟶ ℰom(𝒪_Z, F)|_{i^{-1}U}` of `𝒪_Z`-modules on the opens contained in
`i^{-1}U`.  This is where sections of an internal Hom being morphisms of restrictions is
used. -/
def sliceEquiv (h : S.PushforwardInternalHom) (N : SheafOfModules.{u} (structureSheafRing S.Z))
    (F : SheafOfModules.{u} (structureSheafRing S.X)) (U : Opens S.X) :
    (((modulePushforward S.i).obj N).over U ⟶ F.over U) ≃+
      (N.over (S.openPreimage U) ⟶
        (S.sheafHomExactSupport.obj F).over (S.openPreimage U)) where
  toFun w := ⟨(((h.iso N).hom.app F).val.app (op U)).hom w.val⟩
  invFun z := ⟨(((h.iso N).inv.app F).val.app (op U)).hom z.val⟩
  left_inv w := SheafOfModules.hom_ext <|
    congrArg (fun t : _ ⟶ _ => (t.val.app (op U)).hom w.val) ((h.iso N).hom_inv_id_app F)
  right_inv z := SheafOfModules.hom_ext <|
    congrArg (fun t : _ ⟶ _ => (t.val.app (op U)).hom z.val) ((h.iso N).inv_hom_id_app F)
  map_add' w w' := SheafOfModules.hom_ext <|
    map_add (((h.iso N).hom.app F).val.app (op U)).hom w.val w'.val

/-- On the underlying morphisms of presheaves of modules, the identification of sections is the
underived identification evaluated at `U`. -/
theorem sliceEquiv_val (h : S.PushforwardInternalHom)
    (N : SheafOfModules.{u} (structureSheafRing S.Z))
    (F : SheafOfModules.{u} (structureSheafRing S.X)) (U : Opens S.X)
    (w : ((modulePushforward S.i).obj N).over U ⟶ F.over U) :
    (h.sliceEquiv N F U w).val = (((h.iso N).hom.app F).val.app (op U)).hom w.val :=
  rfl

/-- On the underlying morphisms of presheaves of modules, the inverse identification of sections
is the inverse of the underived identification evaluated at `U`. -/
theorem sliceEquiv_symm_val (h : S.PushforwardInternalHom)
    (N : SheafOfModules.{u} (structureSheafRing S.Z))
    (F : SheafOfModules.{u} (structureSheafRing S.X))
    (U : Opens S.X)
    (z : N.over (S.openPreimage U) ⟶
      (S.sheafHomExactSupport.obj F).over (S.openPreimage U)) :
    ((h.sliceEquiv N F U).symm z).val = (((h.iso N).inv.app F).val.app (op U)).hom z.val :=
  rfl

/-- The inverse identification of sections turns postcomposition with `ℰom(𝒪_Z, f)` into
postcomposition with `f`. -/
theorem sliceEquiv_symm_comp (h : S.PushforwardInternalHom)
    (N : SheafOfModules.{u} (structureSheafRing S.Z))
    {F F' : SheafOfModules.{u} (structureSheafRing S.X)} (f : F ⟶ F') (U : Opens S.X)
    (z : N.over (S.openPreimage U) ⟶
      (S.sheafHomExactSupport.obj F).over (S.openPreimage U)) :
    (h.sliceEquiv N F' U).symm
        (z ≫ (S.sheafHomExactSupport.map f).over (S.openPreimage U)) =
      (h.sliceEquiv N F U).symm z ≫ f.over U :=
  SheafOfModules.hom_ext <|
    congrArg (fun t : _ ⟶ _ => (t.val.app (op U)).hom z.val) ((h.iso N).inv.naturality f)

/-- The inverse identification of sections turns precomposition with `g` into precomposition
with `i_*g`. -/
theorem sliceEquiv_symm_precomp (h : S.PushforwardInternalHom)
    {N N' : SheafOfModules.{u} (structureSheafRing S.Z)} (g : N ⟶ N')
    (F : SheafOfModules.{u} (structureSheafRing S.X)) (U : Opens S.X)
    (z : N'.over (S.openPreimage U) ⟶
      (S.sheafHomExactSupport.obj F).over (S.openPreimage U)) :
    (h.sliceEquiv N F U).symm (g.over (S.openPreimage U) ≫ z) =
      ((modulePushforward S.i).map g).over U ≫ (h.sliceEquiv N' F U).symm z :=
  SheafOfModules.hom_ext
    (congrArg (fun t : _ ⟶ _ => (t.val.app (op U)).hom z.val) (h.natural_inv g F)).symm

/-- The inverse identification of sections commutes with the action of the units of `ℤ`. -/
theorem sliceEquiv_symm_units_smul (h : S.PushforwardInternalHom)
    (N : SheafOfModules.{u} (structureSheafRing S.Z))
    (F : SheafOfModules.{u} (structureSheafRing S.X))
    (U : Opens S.X) (c : ℤˣ)
    (z : N.over (S.openPreimage U) ⟶
      (S.sheafHomExactSupport.obj F).over (S.openPreimage U)) :
    (h.sliceEquiv N F U).symm (c • z) = c • (h.sliceEquiv N F U).symm z := by
  obtain rfl | rfl := Int.units_eq_one_or c
  · rw [one_smul, one_smul]
  · rw [Units.neg_smul, Units.neg_smul, one_smul, one_smul, map_neg]

/-- The inverse identification of sections is compatible with restriction to a smaller open:
two sections agreeing after restriction have identifications agreeing after restriction. -/
theorem inv_app_app_restrict (h : S.PushforwardInternalHom)
    (N : SheafOfModules.{u} (structureSheafRing S.Z))
    (F : SheafOfModules.{u} (structureSheafRing S.X))
    {U V : Opens S.X} (hVU : V ≤ U)
    (zU : ((modulePushforward S.i).obj
      ((Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor.{u, u, u, u}
        (Opens.grothendieckTopology S.Z.carrier) S.Z.sheaf N).obj
          (S.sheafHomExactSupport.obj F))).val.obj (op U))
    (zV : ((modulePushforward S.i).obj
      ((Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor.{u, u, u, u}
        (Opens.grothendieckTopology S.Z.carrier) S.Z.sheaf N).obj
          (S.sheafHomExactSupport.obj F))).val.obj (op V))
    (hz : (((modulePushforward S.i).obj
      ((Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor.{u, u, u, u}
        (Opens.grothendieckTopology S.Z.carrier) S.Z.sheaf N).obj
          (S.sheafHomExactSupport.obj F))).val.map (homOfLE hVU).op) zU = zV)
    {W : Opens S.X} (hWV : W ≤ V)
    (x : ((modulePushforward S.i).obj N).val.obj (op W)) :
    PresheafOfModules.Hom.app ((((h.iso N).inv.app F).val.app (op U)) zU)
        (op (Over.mk (homOfLE (le_trans hWV hVU)))) x =
      PresheafOfModules.Hom.app ((((h.iso N).inv.app F).val.app (op V)) zV)
        (op (Over.mk (homOfLE hWV))) x := by
  subst hz
  refine Eq.trans ?_ (congrArg
    (fun t : _ ⟶ _ ↦ PresheafOfModules.Hom.app t (op (Over.mk (homOfLE hWV))) x)
      (PresheafOfModules.naturality_apply ((h.iso N).inv.app F).val
        (homOfLE hVU).op zU)).symm
  exact (Stacks.PresheafOfModules.InternalHom.internalHom_map_app_apply S.X.sheaf.obj
    ((modulePushforward S.i).obj N).val F.val (homOfLE hVU) _
    (Over.mk (homOfLE hWV)) x).symm

/-- The inverse identification of sections is `𝒪_X(U)`-linear: scaling a section scales the
cochain it is identified with, which on a smaller open is scaling by the restricted scalar. -/
theorem inv_app_app_smul (h : S.PushforwardInternalHom)
    (N : SheafOfModules.{u} (structureSheafRing S.Z))
    (F : SheafOfModules.{u} (structureSheafRing S.X))
    (U : Opens S.X) (r : (structureSheafRing S.X).obj.obj (op U))
    (zr z : ((modulePushforward S.i).obj
      ((Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor.{u, u, u, u}
        (Opens.grothendieckTopology S.Z.carrier) S.Z.sheaf N).obj
          (S.sheafHomExactSupport.obj F))).val.obj (op U))
    (hz : zr = r • z)
    {W : Opens S.X} (hWU : W ≤ U) (x : ((modulePushforward S.i).obj N).val.obj (op W)) :
    PresheafOfModules.Hom.app ((((h.iso N).inv.app F).val.app (op U)) zr)
        (op (Over.mk (homOfLE hWU))) x =
      (structureSheafRing S.X).obj.map (homOfLE hWU).op r •
        PresheafOfModules.Hom.app ((((h.iso N).inv.app F).val.app (op U)) z)
          (op (Over.mk (homOfLE hWU))) x := by
  subst hz
  exact congrArg (fun t : _ ⟶ _ ↦ PresheafOfModules.Hom.app t (op (Over.mk (homOfLE hWU))) x)
    ((((h.iso N).inv.app F).val.app (op U)).hom.map_smul r z)

section Complexes

variable (h : S.PushforwardInternalHom)
  (M : CochainComplex (SheafOfModules.{u} (structureSheafRing S.Z)) ℤ)
  (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ)

/-- The identification of sections, in a fixed cochain degree: a cochain
`(i_*M)|_U ⟶ I|_U` on `X` is the same thing as a cochain
`M|_{i^{-1}U} ⟶ ℰom^•(𝒪_Z, I)|_{i^{-1}U}` on `Z`. -/
def cochainEquiv (U : Opens S.X) (n : ℤ) :
    Cochain (restrictComplex S.Z.sheaf M (S.openPreimage U))
        (restrictComplex S.Z.sheaf
          ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
          (S.openPreimage U)) n ≃+
      Cochain (restrictComplex S.X.sheaf
          (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) U)
        (restrictComplex S.X.sheaf I U) n where
  toFun z := Cochain.mk fun p q hpq => (h.sliceEquiv (M.X p) (I.X q) U).symm (z.v p q hpq)
  invFun w := Cochain.mk fun p q hpq => h.sliceEquiv (M.X p) (I.X q) U (w.v p q hpq)
  left_inv z := by
    refine Cochain.ext _ _ fun p q hpq => ?_
    exact (h.sliceEquiv (M.X p) (I.X q) U).apply_symm_apply (z.v p q hpq)
  right_inv w := by
    refine Cochain.ext _ _ fun p q hpq => ?_
    exact (h.sliceEquiv (M.X p) (I.X q) U).symm_apply_apply (w.v p q hpq)
  map_add' z z' := by
    refine Cochain.ext _ _ fun p q hpq => ?_
    exact map_add (h.sliceEquiv (M.X p) (I.X q) U).symm (z.v p q hpq) (z'.v p q hpq)

/-- The components of the identification of cochains are the identifications of sections. -/
theorem cochainEquiv_apply_v (U : Opens S.X) (n : ℤ)
    (z : Cochain (restrictComplex S.Z.sheaf M (S.openPreimage U))
      (restrictComplex S.Z.sheaf
        ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
        (S.openPreimage U)) n) (p q : ℤ) (hpq : p + n = q) :
    (h.cochainEquiv M I U n z).v p q hpq =
      (h.sliceEquiv (M.X p) (I.X q) U).symm (z.v p q hpq) :=
  rfl

/-- The identification of sections turns postcomposition with the differential of
`ℰom^•(𝒪_Z, I)` into postcomposition with the differential of `I`. -/
theorem sliceEquiv_symm_comp_d (U : Opens S.X) (p q' q : ℤ)
    (z : (restrictComplex S.Z.sheaf M (S.openPreimage U)).X p ⟶
      (restrictComplex S.Z.sheaf
        ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
        (S.openPreimage U)).X q') :
    (h.sliceEquiv (M.X p) (I.X q) U).symm
        (z ≫ (restrictComplex S.Z.sheaf
          ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
          (S.openPreimage U)).d q' q) =
      (h.sliceEquiv (M.X p) (I.X q') U).symm z ≫ (restrictComplex S.X.sheaf I U).d q' q :=
  h.sliceEquiv_symm_comp (M.X p) (I.d q' q) U z

/-- The identification of sections turns precomposition with the differential of `M` into
precomposition with the differential of `i_*M`. -/
theorem sliceEquiv_symm_precomp_d (U : Opens S.X) (p p' q : ℤ)
    (z : (restrictComplex S.Z.sheaf M (S.openPreimage U)).X p' ⟶
      (restrictComplex S.Z.sheaf
        ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
        (S.openPreimage U)).X q) :
    (h.sliceEquiv (M.X p) (I.X q) U).symm
        ((restrictComplex S.Z.sheaf M (S.openPreimage U)).d p p' ≫ z) =
      (restrictComplex S.X.sheaf
          (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) U).d p p' ≫
        (h.sliceEquiv (M.X p') (I.X q) U).symm z :=
  h.sliceEquiv_symm_precomp (M.d p p') (I.X q) U z

/-- The identification of sections is additive, stated at the source and target the differential
of the Hom complex produces.

`sliceEquiv` is an additive equivalence, so this is `map_add`; what it adds is the spelling.
The addition of the two morphism groups is spelled over the degrees of the restricted complexes
here and over the restrictions of the individual sheaves of modules in the type of `sliceEquiv`,
and only the first spelling occurs in the differential of the Hom complex. -/
private theorem sliceEquiv_symm_add (U : Opens S.X) (p q : ℤ)
    (z z' : (restrictComplex S.Z.sheaf M (S.openPreimage U)).X p ⟶
      (restrictComplex S.Z.sheaf
        ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
        (S.openPreimage U)).X q) :
    (h.sliceEquiv (M.X p) (I.X q) U).symm (z + z') =
      (h.sliceEquiv (M.X p) (I.X q) U).symm z + (h.sliceEquiv (M.X p) (I.X q) U).symm z' :=
  map_add (h.sliceEquiv (M.X p) (I.X q) U).symm z z'

/-- The identification of sections commutes with the action of the units of `ℤ`, stated at the
source and target the differential of the Hom complex produces.  This is
`sliceEquiv_symm_units_smul` in the spelling of `sliceEquiv_symm_add`. -/
private theorem sliceEquiv_symm_units_smul_restrict (U : Opens S.X) (p q : ℤ) (c : ℤˣ)
    (z : (restrictComplex S.Z.sheaf M (S.openPreimage U)).X p ⟶
      (restrictComplex S.Z.sheaf
        ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
        (S.openPreimage U)).X q) :
    (h.sliceEquiv (M.X p) (I.X q) U).symm (c • z) =
      c • (h.sliceEquiv (M.X p) (I.X q) U).symm z :=
  h.sliceEquiv_symm_units_smul (M.X p) (I.X q) U c z

/-- The identification of cochains commutes with the differential of the Hom complex. -/
theorem cochainEquiv_δ (U : Opens S.X) (n m : ℤ) (hnm : n + 1 = m)
    (z : Cochain (restrictComplex S.Z.sheaf M (S.openPreimage U))
      (restrictComplex S.Z.sheaf
        ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
        (S.openPreimage U)) n) :
    h.cochainEquiv M I U m (δ n m z) = δ n m (h.cochainEquiv M I U n z) := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  have hA : (h.sliceEquiv (M.X p) (I.X q) U).symm
        (z.v p (q - 1) (by omega) ≫
          (restrictComplex S.Z.sheaf
            ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
            (S.openPreimage U)).d (q - 1) q) =
      (h.cochainEquiv M I U n z).v p (q - 1) (by omega) ≫
        (restrictComplex S.X.sheaf I U).d (q - 1) q :=
    (h.sliceEquiv_symm_comp_d M I U p (q - 1) q (z.v p (q - 1) (by omega))).trans
      (congrArg (fun t ↦ t ≫ (restrictComplex S.X.sheaf I U).d (q - 1) q)
        (h.cochainEquiv_apply_v M I U n z p (q - 1) (by omega)).symm)
  have hB : (h.sliceEquiv (M.X p) (I.X q) U).symm
        ((restrictComplex S.Z.sheaf M (S.openPreimage U)).d p (p + 1) ≫
          z.v (p + 1) q (by omega)) =
      (restrictComplex S.X.sheaf
          (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) U).d
            p (p + 1) ≫
        (h.cochainEquiv M I U n z).v (p + 1) q (by omega) :=
    (h.sliceEquiv_symm_precomp_d M I U p (p + 1) q (z.v (p + 1) q (by omega))).trans
      (congrArg (fun t ↦ (restrictComplex S.X.sheaf
            (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) U).d
              p (p + 1) ≫ t)
        (h.cochainEquiv_apply_v M I U n z (p + 1) q (by omega)).symm)
  rw [h.cochainEquiv_apply_v M I U m (δ n m z) p q hpq,
    δ_v n m hnm z p q hpq (q - 1) (p + 1) rfl rfl,
    δ_v n m hnm (h.cochainEquiv M I U n z) p q hpq (q - 1) (p + 1) rfl rfl,
    h.sliceEquiv_symm_add M I U p q,
    h.sliceEquiv_symm_units_smul_restrict M I U p q]
  exact Eq.trans
    (congrArg (fun t ↦ t + m.negOnePow • (h.sliceEquiv (M.X p) (I.X q) U).symm
        ((restrictComplex S.Z.sheaf M (S.openPreimage U)).d p (p + 1) ≫
          z.v (p + 1) q (by omega))) hA)
    (congrArg (fun t ↦ (h.cochainEquiv M I U n z).v p (q - 1) (by omega) ≫
        (restrictComplex S.X.sheaf I U).d (q - 1) q + m.negOnePow • t) hB)

end Complexes

end PushforwardInternalHom

section Realization

variable {S}
variable (h : S.PushforwardInternalHom)
  (M : CochainComplex (SheafOfModules.{u} (structureSheafRing S.Z)) ℤ)
  (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ)

/-- The complex `i_*(SheafHom^•_Z(M, ℰom^•(𝒪_Z, I)))` of `𝒪_X`-modules. -/
abbrev pushforwardSheafHomObj : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ :=
  ((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (Stacks.SheafOfModules.sheafHomComplex S.Z.sheaf M
      ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).obj

/-- The identification of sections of `i_*(SheafHom^•_Z(M, ℰom^•(𝒪_Z, I)))` over `U` with the
Hom complex of the restrictions `(i_*M)|_U ⟶ I|_U`, in a fixed cochain degree. -/
def pushforwardSectionsIsoApp (U : Opens S.X) (n : ℤ) :
    (Stacks.SheafOfModules.sectionComplex S.X.sheaf (pushforwardSheafHomObj M I) U).X n ≅
      ((Stacks.SheafOfModules.restrictComplex S.X.sheaf
          (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) U).HomComplex
        (Stacks.SheafOfModules.restrictComplex S.X.sheaf I U)).X n :=
  HomologicalComplex.Hom.isoApp
      ((Stacks.SheafOfModules.sheafHomComplex S.Z.sheaf M
        ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).sectionsIso
          (S.openPreimage U)) n ≪≫
    { hom := AddCommGrpCat.ofHom (h.cochainEquiv M I U n).toAddMonoidHom
      inv := AddCommGrpCat.ofHom (h.cochainEquiv M I U n).symm.toAddMonoidHom
      hom_inv_id := by
        ext z
        exact (h.cochainEquiv M I U n).symm_apply_apply z
      inv_hom_id := by
        ext z
        exact (h.cochainEquiv M I U n).apply_symm_apply z }

/-- The cochain attached to a section of `i_*(SheafHom^•_Z(M, ℰom^•(𝒪_Z, I)))` over `U`:
read the section as a cochain on `i^{-1}U` through the realization on `Z`, then identify each
component. -/
theorem pushforwardSectionsIsoApp_hom_apply (U : Opens S.X) (n : ℤ)
    (s : ((pushforwardSheafHomObj M I).X n).val.obj (op U)) :
    AddCommGrpCat.Hom.hom (pushforwardSectionsIsoApp h M I U n).hom s =
      h.cochainEquiv M I U n (AddCommGrpCat.Hom.hom
        (((Stacks.SheafOfModules.sheafHomComplex S.Z.sheaf M
          ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).sectionsIso
            (S.openPreimage U)).hom.f n) s) :=
  rfl

/-- The identification of sections of `i_*(SheafHom^•_Z(M, ℰom^•(𝒪_Z, I)))` over `U` with the
Hom complex of the restrictions `(i_*M)|_U ⟶ I|_U`, as an isomorphism of complexes of abelian
groups. -/
def pushforwardSectionsIso (U : Opens S.X) :
    Stacks.SheafOfModules.sectionComplex S.X.sheaf (pushforwardSheafHomObj M I) U ≅
      (Stacks.SheafOfModules.restrictComplex S.X.sheaf
          (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) U).HomComplex
        (Stacks.SheafOfModules.restrictComplex S.X.sheaf I U) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => pushforwardSectionsIsoApp h M I U n) (by
    intro n m hnm
    ext s
    have hz := congrArg (fun t : _ ⟶ _ => AddCommGrpCat.Hom.hom t s)
      (((Stacks.SheafOfModules.sheafHomComplex S.Z.sheaf M
        ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).sectionsIso
          (S.openPreimage U)).hom.comm n m)
    exact (h.cochainEquiv_δ M I U n m hnm _).symm.trans
      (congrArg (h.cochainEquiv M I U m) hz))

/-- The component at `(p, q)` of the cochain attached to a section over `U`. -/
theorem pushforwardSectionsIso_hom_f_apply_v (U : Opens S.X) (n : ℤ)
    (s : ((pushforwardSheafHomObj M I).X n).val.obj (op U)) (p q : ℤ) (hpq : p + n = q) :
    (AddCommGrpCat.Hom.hom ((pushforwardSectionsIso h M I U).hom.f n) s).v p q hpq =
      (h.sliceEquiv (M.X p) (I.X q) U).symm
        ((AddCommGrpCat.Hom.hom
          (((Stacks.SheafOfModules.sheafHomComplex S.Z.sheaf M
            ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              I)).sectionsIso (S.openPreimage U)).hom.f n) s).v p q hpq) :=
  rfl

/-- **Stacks 0E2I at the level of complexes.**  The complex
`i_*(SheafHom^•_Z(M, ℰom^•(𝒪_Z, I)))` realizes the internal Hom complex
`SheafHom^•_X(i_*M, I)`: its sections over an open `U ⊆ X` are the Hom complex of the
restrictions `(i_*M)|_U ⟶ I|_U`, compatibly with further restriction and with the action of
`𝒪_X(U)`. -/
def pushforwardSheafHomRealization :
    Stacks.SheafOfModules.SheafHomComplex S.X.sheaf
      (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) I where
  obj := pushforwardSheafHomObj M I
  sectionsIso U := pushforwardSectionsIso h M I U
  restrict_natural := by
    intro U V hVU n p q hpq s W hWV x
    rw [pushforwardSectionsIso_hom_f_apply_v h M I U n s p q hpq,
      pushforwardSectionsIso_hom_f_apply_v h M I V n _ p q hpq]
    refine h.inv_app_app_restrict (M.X p) (I.X q) hVU _ _ ?_ hWV x
    apply PresheafOfModules.hom_ext
    intro W'
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    exact (Stacks.SheafOfModules.sheafHomComplex S.Z.sheaf M
      ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).restrict_natural
        (S.openPreimage_le_openPreimage hVU) n p q hpq s (leOfHom W'.unop.hom) y
  smul_natural := by
    intro U r n p q hpq s W hWU x
    rw [pushforwardSectionsIso_hom_f_apply_v h M I U n (r • s) p q hpq,
      pushforwardSectionsIso_hom_f_apply_v h M I U n s p q hpq]
    refine h.inv_app_app_smul (M.X p) (I.X q) U r _ _ ?_ hWU x
    apply PresheafOfModules.hom_ext
    intro W'
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    exact (Stacks.SheafOfModules.sheafHomComplex S.Z.sheaf M
      ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).smul_natural
        (S.openPreimage U) ((structureSheafHom S.i).hom.app (op U) r) n p q hpq s
        (leOfHom W'.unop.hom) y

end Realization

section Comparison

variable {S}
variable (h : S.PushforwardInternalHom)
  (c : Stacks.SheafOfModules.SheafHomComplexComparison S.X.sheaf)

/-- **Stacks 0E2I at the level of complexes.**  The isomorphism of complexes of `𝒪_X`-modules
`i_*(SheafHom^•_Z(M, ℰom^•(𝒪_Z, I))) ≅ SheafHom^•_X(i_*M, I)` comparing the realization above
with the canonical internal Hom complex. -/
def pushforwardSheafHomComplexIso
    (M : CochainComplex (SheafOfModules.{u} (structureSheafRing S.Z)) ℤ)
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) :
    pushforwardSheafHomObj M I ≅
      (Stacks.SheafOfModules.sheafHomComplex S.X.sheaf
        (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) I).obj :=
  c.iso _ _ (pushforwardSheafHomRealization h M I)
    (Stacks.SheafOfModules.sheafHomComplex S.X.sheaf
      (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) I)

/-- On sections over an open `U`, the comparison matches the identification of sections of the
pushforward with the canonical identification of sections. -/
theorem pushforwardSheafHomComplexIso_sections
    (M : CochainComplex (SheafOfModules.{u} (structureSheafRing S.Z)) ℤ)
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) (U : Opens S.X) (n : ℤ)
    (s : ((pushforwardSheafHomObj M I).X n).val.obj (op U)) :
    AddCommGrpCat.Hom.hom
        (((Stacks.SheafOfModules.sheafHomComplex S.X.sheaf
          (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
            I).sectionsIso U).hom.f n)
        (((pushforwardSheafHomComplexIso h c M I).hom.f n).val.app (op U) s) =
      AddCommGrpCat.Hom.hom ((pushforwardSectionsIso h M I U).hom.f n) s :=
  c.sectionsIso_hom _ _ (pushforwardSheafHomRealization h M I) _ U n s

/-- The component at `(p, q)` of the cochain the canonical internal Hom complex attaches to the
image of a section of the pushforward realization: it is the identification of sections of the
`𝒪_Z`-side internal Hom complex, followed in that component by the identification of
sections of the underived Stacks 0E2I isomorphism. -/
theorem pushforwardSheafHomComplexIso_sections_v
    (M : CochainComplex (SheafOfModules.{u} (structureSheafRing S.Z)) ℤ)
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) (U : Opens S.X) (n : ℤ)
    (s : ((pushforwardSheafHomObj M I).X n).val.obj (op U)) (p q : ℤ) (hpq : p + n = q) :
    (AddCommGrpCat.Hom.hom
        (((Stacks.SheafOfModules.sheafHomComplex S.X.sheaf
          (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
            I).sectionsIso U).hom.f n)
        (((pushforwardSheafHomComplexIso h c M I).hom.f n).val.app (op U) s)).v p q hpq =
      (h.sliceEquiv (M.X p) (I.X q) U).symm
        ((AddCommGrpCat.Hom.hom
          (((Stacks.SheafOfModules.sheafHomComplex S.Z.sheaf M
            ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              I)).sectionsIso (S.openPreimage U)).hom.f n) s).v p q hpq) := by
  rw [pushforwardSheafHomComplexIso_sections h c M I U n s]
  exact pushforwardSectionsIso_hom_f_apply_v h M I U n s p q hpq

/-- The same component formula for a section first moved by the pushforward of a morphism of
the `𝒪_Z`-side internal Hom complexes: on sections such a pushforward is the morphism itself,
read over the preimage open. -/
theorem pushforwardSheafHomComplexIso_sections_v_comp
    (M₀ M : CochainComplex (SheafOfModules.{u} (structureSheafRing S.Z)) ℤ)
    (I₀ I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ)
    (ψ : (Stacks.SheafOfModules.sheafHomComplex S.Z.sheaf M₀
          ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I₀)).obj ⟶
      (Stacks.SheafOfModules.sheafHomComplex S.Z.sheaf M
        ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).obj)
    (U : Opens S.X) (n : ℤ) (s : ((pushforwardSheafHomObj M₀ I₀).X n).val.obj (op U))
    (p q : ℤ) (hpq : p + n = q) :
    (AddCommGrpCat.Hom.hom
        (((Stacks.SheafOfModules.sheafHomComplex S.X.sheaf
          (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
            I).sectionsIso U).hom.f n)
        (((((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).map ψ ≫
            (pushforwardSheafHomComplexIso h c M I).hom).f n).val.app (op U) s)).v p q hpq =
      (h.sliceEquiv (M.X p) (I.X q) U).symm
        ((AddCommGrpCat.Hom.hom
          (((Stacks.SheafOfModules.sheafHomComplex S.Z.sheaf M
            ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              I)).sectionsIso (S.openPreimage U)).hom.f n)
          ((ψ.f n).val.app (op (S.openPreimage U)) s)).v p q hpq) :=
  pushforwardSheafHomComplexIso_sections_v h c M I U n
    (((((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).map ψ).f n).val.app
      (op U) s) p q hpq

/-- **Postcomposition in the second variable, read through the identification of sections.**
The cochain attached to a section over `U` of `i_*(SheafHom^•_Z(M, ℰom^•(𝒪_Z, I)))`, followed
over `i^{-1}U` by the component of `ℰom^•(𝒪_Z, f)` for `f : I ⟶ I'`, is the cochain attached to
the same section followed over `U` by the component of `f`. -/
theorem pushforwardSectionsIso_comp_v
    (M : CochainComplex (SheafOfModules.{u} (structureSheafRing S.Z)) ℤ)
    {I I' : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ} (f : I ⟶ I')
    (U : Opens S.X) (n : ℤ) (s : ((pushforwardSheafHomObj M I).X n).val.obj (op U))
    (p q : ℤ) (hpq : p + n = q) :
    (h.sliceEquiv (M.X p) (I'.X q) U).symm
        (SheafOfModules.Hom.over (HomologicalComplex.Hom.f (𝟙 M) p) (S.openPreimage U) ≫
          (AddCommGrpCat.Hom.hom
              (((Stacks.SheafOfModules.sheafHomComplex S.Z.sheaf M
                ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                  I)).sectionsIso (S.openPreimage U)).hom.f n) s).v p q hpq ≫
            SheafOfModules.Hom.over
              (((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).map f).f q)
              (S.openPreimage U)) =
      SheafOfModules.Hom.over
          (HomologicalComplex.Hom.f
            (𝟙 (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) p)
          U ≫
        (AddCommGrpCat.Hom.hom ((pushforwardSectionsIso h M I U).hom.f n) s).v p q hpq ≫
          SheafOfModules.Hom.over (f.f q) U := by
  have e1 : SheafOfModules.Hom.over (HomologicalComplex.Hom.f (𝟙 M) p)
      (S.openPreimage U) = 𝟙 _ :=
    (SheafOfModules.overFunctor (structureSheafRing S.Z) (S.openPreimage U)).map_id _
  have e2 : SheafOfModules.Hom.over
      (HomologicalComplex.Hom.f
        (𝟙 (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) p)
      U = 𝟙 _ := (SheafOfModules.overFunctor (structureSheafRing S.X) U).map_id _
  rw [e1, Category.id_comp, e2, Category.id_comp,
    pushforwardSectionsIso_hom_f_apply_v h M I U n s p q hpq]
  exact h.sliceEquiv_symm_comp (M.X p) (f.f q) U _

/-- **Precomposition in the first variable, read through the identification of sections.**  The
cochain attached to a section over `U` of `i_*(SheafHom^•_Z(M, ℰom^•(𝒪_Z, I)))`, preceded over
`i^{-1}U` by the component of `g : M' ⟶ M`, is the cochain attached to the same section preceded
over `U` by the component of `i_* g`. -/
theorem pushforwardSectionsIso_precomp_v
    {M M' : CochainComplex (SheafOfModules.{u} (structureSheafRing S.Z)) ℤ} (g : M' ⟶ M)
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ)
    (U : Opens S.X) (n : ℤ) (s : ((pushforwardSheafHomObj M I).X n).val.obj (op U))
    (p q : ℤ) (hpq : p + n = q) :
    (h.sliceEquiv (M'.X p) (I.X q) U).symm
        (SheafOfModules.Hom.over (g.f p) (S.openPreimage U) ≫
          (AddCommGrpCat.Hom.hom
              (((Stacks.SheafOfModules.sheafHomComplex S.Z.sheaf M
                ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                  I)).sectionsIso (S.openPreimage U)).hom.f n) s).v p q hpq) =
      SheafOfModules.Hom.over
          (HomologicalComplex.Hom.f
            (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).map g) p) U ≫
        (AddCommGrpCat.Hom.hom ((pushforwardSectionsIso h M I U).hom.f n) s).v p q hpq :=
  h.sliceEquiv_symm_precomp (g.f p) (I.X q) U _

/-- The comparison is natural in both variables at once: for `g : M' ⟶ M` and `f : I ⟶ I'`, it
carries `i_*(SheafHom^•_Z(g, ℰom^•(𝒪_Z, f)))` to `SheafHom^•_X(i_* g, f)`. -/
private theorem pushforwardSheafHomComplexIso_natural
    {M M' : CochainComplex (SheafOfModules.{u} (structureSheafRing S.Z)) ℤ}
    {I I' : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ} (g : M' ⟶ M)
    (f : I ⟶ I') :
    (pushforwardSheafHomComplexIso h c M I).hom ≫
        Stacks.SheafOfModules.sheafHomComplexMap S.X.sheaf
          (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).map g) f =
      ((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (Stacks.SheafOfModules.sheafHomComplexMap S.Z.sheaf g
            ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).map f)) ≫
        (pushforwardSheafHomComplexIso h c M' I').hom := by
  refine Stacks.SheafOfModules.SheafHomComplex.eq_of_isInducedMap S.X.sheaf
    (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).map g) f
    (pushforwardSheafHomRealization h M I)
    (Stacks.SheafOfModules.sheafHomComplex S.X.sheaf
      (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj M') I') ?_ ?_
  · intro U n p q hpq s
    have hstep := Stacks.SheafOfModules.sheafHomComplexMap_isInduced S.X.sheaf
      (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).map g) f U n p q
      hpq (((pushforwardSheafHomComplexIso h c M I).hom.f n).val.app (op U) s)
    rw [pushforwardSheafHomComplexIso_sections h c M I U n s] at hstep
    exact hstep
  · intro U n p q hpq s
    have hZ := Stacks.SheafOfModules.sheafHomComplexMap_isInduced S.Z.sheaf g
      ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
      (S.openPreimage U) n p q hpq s
    refine Eq.trans (pushforwardSheafHomComplexIso_sections_v_comp h c M M' I I'
      (Stacks.SheafOfModules.sheafHomComplexMap S.Z.sheaf g
        ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).map f))
      U n s p q hpq) ?_
    rw [hZ, h.sliceEquiv_symm_precomp]
    exact congrArg _ (h.sliceEquiv_symm_comp (M.X p) (f.f q) U _)

/-- **The comparison is natural in the complex of `𝒪_X`-modules.**  A morphism `f : I ⟶ I'`
induces `i_*(SheafHom^•_Z(M, ℰom^•(𝒪_Z, f)))` on the pushforward realization and
`SheafHom^•_X(i_*M, f)` on the canonical internal Hom complex, and the comparison carries the
first to the second. -/
theorem pushforwardSheafHomComplexIso_natural_right
    (M : CochainComplex (SheafOfModules.{u} (structureSheafRing S.Z)) ℤ)
    {I I' : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ} (f : I ⟶ I') :
    (pushforwardSheafHomComplexIso h c M I).hom ≫
        Stacks.SheafOfModules.sheafHomComplexMap S.X.sheaf
          (𝟙 (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) f =
      ((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (Stacks.SheafOfModules.sheafHomComplexMap S.Z.sheaf (𝟙 M)
            ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).map f)) ≫
        (pushforwardSheafHomComplexIso h c M I').hom := by
  have := pushforwardSheafHomComplexIso_natural h c (𝟙 M) f
  rwa [CategoryTheory.Functor.map_id] at this

/-- **The comparison is natural in the complex of `𝒪_X`-modules**, with the induced maps
spelled as the site-level `AlgebraicGeometry.RingedSite.homMap` of the two ringed sites. -/
theorem pushforwardSheafHomComplexIso_natural_right_homMap
    (M : CochainComplex (SheafOfModules.{u} (structureSheafRing S.Z)) ℤ)
    {I I' : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ} (f : I ⟶ I') :
    ((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (AlgebraicGeometry.RingedSite.homMap (Stacks.SheafOfModules.ringedSite S.Z.sheaf)
            (𝟙 M) ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).map f)) ≫
        (pushforwardSheafHomComplexIso h c M I').hom =
      (pushforwardSheafHomComplexIso h c M I).hom ≫
        AlgebraicGeometry.RingedSite.homMap (Stacks.SheafOfModules.ringedSite S.X.sheaf)
          (𝟙 (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) f :=
  (by rw [← Stacks.SheafOfModules.sheafHomComplexMap_eq_homMap,
      ← Stacks.SheafOfModules.sheafHomComplexMap_eq_homMap]
      exact (pushforwardSheafHomComplexIso_natural_right h c M f).symm)

/-- **The comparison is natural in the complex of `𝒪_Z`-modules.**  A morphism `g : M' ⟶ M`
induces `i_*(SheafHom^•_Z(g, ℰom^•(𝒪_Z, I)))` on the pushforward realization and
`SheafHom^•_X(i_* g, I)` on the canonical internal Hom complex, and the comparison carries the
first to the second.

The structure `…PushforwardSheafHomComplex` records only the naturality in the complex of
`𝒪_X`-modules, which is all that the extension of the derived identification along a K-injective
resolution of the target needs.  This is the other naturality, which a statement about the
derived identification at a *fixed* object of `D(𝒪_Z)` needs: the derived identification is
built at a chosen cochain representative of that object. -/
theorem pushforwardSheafHomComplexIso_natural_left
    {M M' : CochainComplex (SheafOfModules.{u} (structureSheafRing S.Z)) ℤ} (g : M' ⟶ M)
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) :
    (pushforwardSheafHomComplexIso h c M I).hom ≫
        Stacks.SheafOfModules.sheafHomComplexMap S.X.sheaf
          (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).map g) (𝟙 I) =
      ((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (Stacks.SheafOfModules.sheafHomComplexMap S.Z.sheaf g
            (𝟙 ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) ≫
        (pushforwardSheafHomComplexIso h c M' I).hom := by
  have := pushforwardSheafHomComplexIso_natural h c g (𝟙 I)
  rwa [CategoryTheory.Functor.map_id] at this

/-- **The comparison is natural in the complex of `𝒪_Z`-modules**, with the induced maps spelled
as the site-level `AlgebraicGeometry.RingedSite.homMap` of the two ringed sites. -/
theorem pushforwardSheafHomComplexIso_natural_left_homMap
    {M M' : CochainComplex (SheafOfModules.{u} (structureSheafRing S.Z)) ℤ} (g : M' ⟶ M)
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) :
    ((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (AlgebraicGeometry.RingedSite.homMap (Stacks.SheafOfModules.ringedSite S.Z.sheaf) g
            (𝟙 ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) ≫
        (pushforwardSheafHomComplexIso h c M' I).hom =
      (pushforwardSheafHomComplexIso h c M I).hom ≫
        AlgebraicGeometry.RingedSite.homMap (Stacks.SheafOfModules.ringedSite S.X.sheaf)
          (((modulePushforward S.i).mapHomologicalComplex (ComplexShape.up ℤ)).map g) (𝟙 I) :=
  (by rw [← Stacks.SheafOfModules.sheafHomComplexMap_eq_homMap,
      ← Stacks.SheafOfModules.sheafHomComplexMap_eq_homMap]
      exact (pushforwardSheafHomComplexIso_natural_left h c g I).symm)


end Comparison

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

end
