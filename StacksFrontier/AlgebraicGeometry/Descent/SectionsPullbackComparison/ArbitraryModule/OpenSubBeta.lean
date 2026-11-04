module

public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.ArbitraryModule.LocalSurjectivity

/-!
# Stacks 070S (1) for an arbitrary module: generators and the transpose `β`

The source `AlgebraicGeometry.BigFppfOver.presheafPullback` of the comparison of Stacks 070S (1),
its generators `AlgebraicGeometry.BigFppfOver.presheafPullbackGenerator` and the fact that every
section lies in the span of the generators over one open of `S`; then the opens of an object as
a functor into the big site (`AlgebraicGeometry.BigFppfOver.openSubFunctor`), the ring
comparison `AlgebraicGeometry.BigFppfOver.openSubStructureMap` along it, and the transpose
`AlgebraicGeometry.BigFppfOver.openSubBeta` of the generators, with its values on generators.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry ChangeOfRings

universe u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The comparison on a restricted pulled-back section.**  Over an object `T` of the big site
whose structure morphism factors through an open `U` of `S`, the component of
`AlgebraicGeometry.BigFppfOver.pullbackSectionsComparison` carries the restriction to `T` of the
unit's image of a section `a` of `F` over `U` to the pullback of `a` to `T`.  Together with
`PresheafOfModules.mem_pullbackUnitSubmodule`, which says that these restrictions span, this
determines the comparison on every section of the source.

This is the step inside the proof of
`AlgebraicGeometry.BigFppfOver.surjective_app_sectionsComparison`, stated on its own: naturality
of the comparison along `T ⟶ U`, then
`AlgebraicGeometry.BigFppfOver.pullbackSectionsComparison_unit_app`, then
`AlgebraicGeometry.pullbackSectionsMap_pullbackSectionHom`. -/
public theorem pullbackSectionsComparison_app_map_unit (F : S.Modules)
    {T : BigFppfOver B S hS} {U : S.Opens} (j : T ⟶ (opensToBig B S hS).obj U)
    (hX : (⊤ : ((toScheme B S hS).obj T).Opens) ≤ T.hom.hom ⁻¹ᵁ U)
    (a : ((SheafOfModules.forget S.ringCatSheaf).obj F).obj (op U)) :
    ModuleCat.Hom.hom ((pullbackSectionsComparison B S hS F).app (op T))
        (((PresheafOfModules.pullback.{u} (structureMap B S hS).hom).obj
          ((SheafOfModules.forget S.ringCatSheaf).obj F)).map j.op
            (((PresheafOfModules.pullbackPushforwardAdjunction.{u}
              (structureMap B S hS).hom).unit.app
                ((SheafOfModules.forget S.ringCatSheaf).obj F)).app (op U) a)) =
      (pullbackSectionHom T.hom.hom F U ⊤ hX a :
        Γ((Scheme.Modules.pullback T.hom.hom).obj F, ⊤)) := by
  refine Eq.trans
    (PresheafOfModules.naturality_apply (pullbackSectionsComparison B S hS F) j.op _) ?_
  refine Eq.trans (congrArg (fun z => (pullbackSectionsPresheaf B S hS F).map j.op z)
    (pullbackSectionsComparison_unit_app B S hS F U a)) ?_
  exact pullbackSectionsMap_pullbackSectionHom F
    ((Over.post (X := B.obj hS) B.inclusion).map j) U
    (Scheme.Opens.top_le_ι_preimage le_rfl) hX a

/-- **The source of the comparison of Stacks 070S (1).**  The pullback, as a presheaf of modules,
of a module `F` on `S` along the structure-sheaf comparison of the big fppf site;
`AlgebraicGeometry.BigFppfOver.associatedModuleSheafificationIso` presents the associated module
of `F` as its sheafification. -/
public noncomputable abbrev presheafPullback (F : S.Modules) :
    PresheafOfModules.{u} (structureSheaf B S hS).obj :=
  (PresheafOfModules.pullback.{u} (structureMap B S hS).hom).obj
    ((SheafOfModules.forget S.ringCatSheaf).obj F)

/-- The unit of the pullback--pushforward adjunction at a module `F` on `S`.  Over
an open `U` of `S` it sends a section of `F` to a section of
`AlgebraicGeometry.BigFppfOver.presheafPullback` over the object `U → S` of the big site. -/
public noncomputable abbrev presheafPullbackUnit (F : S.Modules) :
    (SheafOfModules.forget S.ringCatSheaf).obj F ⟶
      (PresheafOfModules.pushforward.{u} (structureMap B S hS).hom).obj
        (presheafPullback B S hS F) :=
  (PresheafOfModules.pullbackPushforwardAdjunction.{u} (structureMap B S hS).hom).unit.app
    ((SheafOfModules.forget S.ringCatSheaf).obj F)

/-- **A generator of the source of the comparison.**  Given an object `T` of the big site
factoring through an open `U` of `S` by `j`, the restriction along `j` of the image under the unit
of a section `a` of `F` over `U`.  These are the elements of
`PresheafOfModules.pullbackUnitGenerators`, so by
`PresheafOfModules.span_pullbackUnitGenerators_eq_top` they span the sections of
`AlgebraicGeometry.BigFppfOver.presheafPullback` over `T`. -/
public noncomputable abbrev presheafPullbackGenerator (F : S.Modules)
    {T : BigFppfOver B S hS} {U : S.Opens} (j : T ⟶ (opensToBig B S hS).obj U) (a : Γ(F, U)) :
    (presheafPullback B S hS F).obj (op T) :=
  (presheafPullback B S hS F).map j.op ((presheafPullbackUnit B S hS F).app (op U) a)

/-- The sections of `AlgebraicGeometry.BigFppfOver.presheafPullback` over an object `T` as a
module over the *commutative* ring `Γ(T, 𝒪_T)`, rather than over the `RingCat` object
`(structureSheaf B S hS).obj.obj (op T)` which carries them.  The two rings and the two module
structures are definitionally equal, but instance search does not cross the identification, and
extension of scalars needs the commutative one. -/
public noncomputable instance module_gamma_presheafPullback (F : S.Modules)
    (T : BigFppfOver B S hS) :
    Module ↥Γ(T.left.obj, ⊤) ↥((presheafPullback B S hS F).obj (op T)) :=
  inferInstanceAs (Module ((structureSheaf B S hS).obj.obj (op T)) _)

/-- **A generator is semilinear in its section.**  Scaling the section of `F` scales the generator
by the restriction of the scalar to the object, the unit being a morphism of presheaves of
modules and restriction being semilinear over the structure sheaf. -/
public theorem presheafPullbackGenerator_smul (F : S.Modules)
    {T : BigFppfOver B S hS} {U : S.Opens} (j : T ⟶ (opensToBig B S hS).obj U)
    (r : Γ(S, U)) (a : Γ(F, U)) :
    presheafPullbackGenerator B S hS F j (r • a) =
      (structureSheaf B S hS).obj.map j.op ((structureMap B S hS).hom.app (op U) r) •
        presheafPullbackGenerator B S hS F j a := by
  refine Eq.trans (congrArg (fun z => (presheafPullback B S hS F).map j.op z)
    (((presheafPullbackUnit B S hS F).app (op U)).hom.map_smul r a)) ?_
  exact PresheafOfModules.map_smul (presheafPullback B S hS F) j.op
    ((structureMap B S hS).hom.app (op U) r) ((presheafPullbackUnit B S hS F).app (op U) a)

/-- The component of `AlgebraicGeometry.BigFppfOver.pullbackSectionsComparison` at an object `T`,
read as a map of modules over `Γ(T, 𝒪_T)` rather than over the `RingCat` object of the structure
sheaf of the big site.  This is the form in which
`AlgebraicGeometry.eq_zero_of_mem_span_of_app_eq_pullbackSection` consumes it; the two module
structures are definitionally equal, so the underlying function is unchanged. -/
public noncomputable def pullbackSectionsComparisonGamma (F : S.Modules)
    (T : BigFppfOver B S hS) :
    ModuleCat.of Γ(T.left.obj, ⊤) ((presheafPullback B S hS F).obj (op T)) ⟶
      ModuleCat.of Γ(T.left.obj, ⊤) Γ((Scheme.Modules.pullback T.hom.hom).obj F, ⊤) :=
  ModuleCat.homEquiv.symm
    { toFun := fun x => (pullbackSectionsComparison B S hS F).app (op T) x
      map_add' := fun x y => map_add ((pullbackSectionsComparison B S hS F).app (op T)).hom x y
      map_smul' := fun c x =>
        ((pullbackSectionsComparison B S hS F).app (op T)).hom.map_smul c x }

/-- A span over the `RingCat` object of the structure sheaf of the big site is a span over
`Γ(T, 𝒪_T)`.  The two rings carry the same action on the same elements, so the two spans have the
same members; but they are submodules over different rings, hence different types, and membership
has to be transported. -/
public theorem mem_span_gamma_of_mem_span_presheafPullbackGenerator (F : S.Modules)
    (T : BigFppfOver B S hS) (G : Set ((presheafPullback B S hS F).obj (op T)))
    {x : (presheafPullback B S hS F).obj (op T)}
    (hx : x ∈ Submodule.span ((structureSheaf B S hS).obj.obj (op T)) G) :
    x ∈ Submodule.span Γ(T.left.obj, ⊤) G := by
  refine Submodule.span_induction (p := fun y _ => y ∈ Submodule.span Γ(T.left.obj, ⊤) G)
    (fun y hy => Submodule.subset_span hy) (Submodule.zero_mem _) ?_ ?_ hx
  · intro p q _ _ hp hq
    exact Submodule.add_mem _ hp hq
  · intro c p _ hp
    exact Submodule.smul_mem _ c hp

/-- Restricting a generator along a morphism of the big site gives the generator over the same
open of `S`: there is at most one morphism to the image of an open of `S`, so the two factorings
agree. -/
public theorem presheafPullbackGenerator_map (F : S.Modules)
    {T T' : BigFppfOver B S hS} (g : T' ⟶ T) {U : S.Opens}
    (j : T ⟶ (opensToBig B S hS).obj U) (j' : T' ⟶ (opensToBig B S hS).obj U) (a : Γ(F, U)) :
    (presheafPullback B S hS F).map g.op (presheafPullbackGenerator B S hS F j a) =
      presheafPullbackGenerator B S hS F j' a := by
  have hj : g ≫ j = j' := Subsingleton.elim _ _
  refine Eq.trans
    (PresheafOfModules.map_comp_apply (presheafPullback B S hS F) j.op g.op _).symm ?_
  exact congrArg (fun k : T' ⟶ (opensToBig B S hS).obj U =>
    (presheafPullback B S hS F).map k.op ((presheafPullbackUnit B S hS F).app (op U) a)) hj

/-- **Shrinking the open of `S`.**  The generator indexed by a section `a` over `U` is the
generator indexed by the restriction of `a` to a smaller open `U'`, as soon as the object still
factors through `U'`: this is naturality of the unit, and again the uniqueness of the
factoring. -/
public theorem presheafPullbackGenerator_map_le (F : S.Modules)
    {T : BigFppfOver B S hS} {U U' : S.Opens} (h : U' ≤ U)
    (j : T ⟶ (opensToBig B S hS).obj U) (j' : T ⟶ (opensToBig B S hS).obj U') (a : Γ(F, U)) :
    presheafPullbackGenerator B S hS F j'
        (((SheafOfModules.forget S.ringCatSheaf).obj F).map (homOfLE h).op a) =
      presheafPullbackGenerator B S hS F j a := by
  refine Eq.trans (congrArg (fun z => (presheafPullback B S hS F).map j'.op z)
    (PresheafOfModules.naturality_apply (presheafPullbackUnit B S hS F) (homOfLE h).op a)) ?_
  exact presheafPullbackGenerator_map B S hS F j' ((opensToBig B S hS).map (homOfLE h)) j a

/-- The span of the generators grows as the open of `S` indexing them shrinks, by
`AlgebraicGeometry.BigFppfOver.presheafPullbackGenerator_map_le`. -/
public theorem span_presheafPullbackGenerator_mono (F : S.Modules)
    {T : BigFppfOver B S hS} {U U' : S.Opens} (h : U' ≤ U)
    (j : T ⟶ (opensToBig B S hS).obj U) (j' : T ⟶ (opensToBig B S hS).obj U') :
    Submodule.span ((structureSheaf B S hS).obj.obj (op T))
        (Set.range fun a : Γ(F, U) => presheafPullbackGenerator B S hS F j a) ≤
      Submodule.span ((structureSheaf B S hS).obj.obj (op T))
        (Set.range fun a : Γ(F, U') => presheafPullbackGenerator B S hS F j' a) := by
  refine Submodule.span_le.2 ?_
  rintro y ⟨a, rfl⟩
  exact Submodule.subset_span ⟨_, presheafPullbackGenerator_map_le B S hS F h j j' a⟩

/-- Restriction along a morphism of the big site carries the span of the generators indexed by an
open of `S` into the span of the generators indexed by the same open. -/
public theorem map_mem_span_presheafPullbackGenerator (F : S.Modules)
    {T T' : BigFppfOver B S hS} (g : T' ⟶ T) {U : S.Opens}
    (j : T ⟶ (opensToBig B S hS).obj U) (j' : T' ⟶ (opensToBig B S hS).obj U)
    {z : (presheafPullback B S hS F).obj (op T)}
    (hz : z ∈ Submodule.span ((structureSheaf B S hS).obj.obj (op T))
      (Set.range fun a : Γ(F, U) => presheafPullbackGenerator B S hS F j a)) :
    (presheafPullback B S hS F).map g.op z ∈
      Submodule.span ((structureSheaf B S hS).obj.obj (op T'))
        (Set.range fun a : Γ(F, U) => presheafPullbackGenerator B S hS F j' a) := by
  refine Submodule.span_induction
    (p := fun y _ => (presheafPullback B S hS F).map g.op y ∈
      Submodule.span ((structureSheaf B S hS).obj.obj (op T'))
        (Set.range fun a : Γ(F, U) => presheafPullbackGenerator B S hS F j' a)) ?_ ?_ ?_ ?_ hz
  · rintro y ⟨a, rfl⟩
    exact Submodule.subset_span ⟨a, (presheafPullbackGenerator_map B S hS F g j j' a).symm⟩
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro p q _ _ hp hq
    rw [map_add]
    exact Submodule.add_mem _ hp hq
  · intro c p _ hp
    rw [PresheafOfModules.map_smul]
    exact Submodule.smul_mem _ _ hp

/-- **Every section of the pullback is a combination of generators over one open of `S`.**
`PresheafOfModules.span_pullbackUnitGenerators_eq_top` writes a section as a combination of
generators indexed by finitely many, possibly different, opens of `S`.  The opens through which
the object factors are closed under intersection — `AlgebraicGeometry.BigFppfOver.homOfRangeLe`
provides the factoring through the intersection — and shrinking the open only enlarges the span,
by `AlgebraicGeometry.BigFppfOver.span_presheafPullbackGenerator_mono`; so the sections admitting
such a description form a submodule, and one open suffices for all of them.

This is the step which makes the rest of local injectivity a single refinement: with one open `W`
in hand the whole argument happens over one covering sieve. -/
public theorem exists_mem_span_presheafPullbackGenerator (F : S.Modules)
    (T : BigFppfOver B S hS) (x : (presheafPullback B S hS F).obj (op T)) :
    ∃ (W : S.Opens) (g : T ⟶ (opensToBig B S hS).obj W),
      x ∈ Submodule.span ((structureSheaf B S hS).obj.obj (op T))
        (Set.range fun a : Γ(F, W) => presheafPullbackGenerator B S hS F g a) := by
  have htop := PresheafOfModules.span_pullbackUnitGenerators_eq_top
    (structureMap B S hS).hom ((SheafOfModules.forget S.ringCatSheaf).obj F) (op T)
  refine Submodule.span_induction
    (p := fun y _ => ∃ (W : S.Opens) (g : T ⟶ (opensToBig B S hS).obj W),
      y ∈ Submodule.span ((structureSheaf B S hS).obj.obj (op T))
        (Set.range fun a : Γ(F, W) => presheafPullbackGenerator B S hS F g a))
    ?_ ?_ ?_ ?_ (htop.ge Submodule.mem_top)
  · rintro y ⟨W, g, a, rfl⟩
    exact ⟨W, g, Submodule.subset_span ⟨a, rfl⟩⟩
  · exact ⟨⊤, homOfRangeLe B S hS ⊤ (by simp), Submodule.zero_mem _⟩
  · rintro y z _ _ ⟨W₁, g₁, hy⟩ ⟨W₂, g₂, hz⟩
    exact ⟨W₁ ⊓ W₂, homOfRangeLe B S hS (W₁ ⊓ W₂)
      (Set.subset_inter (range_le_of_hom B S hS g₁) (range_le_of_hom B S hS g₂)),
      Submodule.add_mem _
      (span_presheafPullbackGenerator_mono B S hS F inf_le_left g₁ _ hy)
      (span_presheafPullbackGenerator_mono B S hS F inf_le_right g₂ _ hz)⟩
  · rintro c y _ ⟨W, g, hy⟩
    exact ⟨W, g, Submodule.smul_mem _ c hy⟩

/-- The inclusion of one open of the underlying scheme of an object of the big site into a larger
one, as a morphism of the big site. -/
@[implicit_reducible]
public noncomputable def openSubObjHom (T : BigFppfOver B S hS) {V V' : T.left.obj.Opens}
    (h : V ≤ V') : openSubObj B S hS T V ⟶ openSubObj B S hS T V' :=
  Over.homMk (ObjectProperty.homMk (X := B.obj (contains_opens B T.left.property V))
      (Y := B.obj (contains_opens B T.left.property V')) (T.left.obj.homOfLE h))
    (by
      apply ObjectProperty.hom_ext
      rw [ObjectProperty.FullSubcategory.comp_hom, openSubObj_hom_hom, openSubObj_hom_hom]
      exact congrArg (fun k : (V : Scheme.{u}) ⟶ T.left.obj => k ≫ T.hom.hom)
        (T.left.obj.homOfLE_ι h))

/-- The morphism of schemes underlying `openSubObjHom T h` is the inclusion
`T.left.obj.homOfLE h` of the smaller open into the larger. -/
@[simp]
public theorem openSubObjHom_left_hom (T : BigFppfOver B S hS) {V V' : T.left.obj.Opens}
    (h : V ≤ V') : (openSubObjHom B S hS T h).left.hom = T.left.obj.homOfLE h := rfl

/-- **The opens of the underlying scheme of an object of the big site, as a functor into the big
site.**  This is the small Zariski site of `AlgebraicGeometry.BigFppfOver.toScheme` of the object,
sitting inside the big site over `S`, exactly as
`AlgebraicGeometry.BigFppfOver.opensToBig` places the small Zariski site of `S` there. -/
public noncomputable def openSubFunctor (T : BigFppfOver B S hS) :
    T.left.obj.Opens ⥤ BigFppfOver B S hS where
  obj V := openSubObj B S hS T V
  map {_ _} h := openSubObjHom B S hS T (leOfHom h)
  map_id V := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    rw [openSubObjHom_left_hom, Over.id_left, ObjectProperty.FullSubcategory.id_hom,
      Scheme.homOfLE_rfl]
    rfl
  map_comp f g := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    rw [openSubObjHom_left_hom, Over.comp_left, ObjectProperty.FullSubcategory.comp_hom,
      openSubObjHom_left_hom, openSubObjHom_left_hom, Scheme.homOfLE_homOfLE]

/-- `openSubFunctor T` sends an open `V` to `openSubObj T V`. -/
@[simp]
public theorem openSubFunctor_obj (T : BigFppfOver B S hS) (V : T.left.obj.Opens) :
    (openSubFunctor B S hS T).obj V = openSubObj B S hS T V := rfl

/-- `openSubFunctor T` sends an inclusion of opens `V ⟶ V'` to `openSubObjHom T`. -/
@[simp]
public theorem openSubFunctor_map (T : BigFppfOver B S hS) {V V' : T.left.obj.Opens}
    (h : V ⟶ V') : (openSubFunctor B S hS T).map h = openSubObjHom B S hS T (leOfHom h) := rfl

/-- **The structure sheaf of the big site, read on the opens of an object.**  The comparison of
the structure sheaf of the underlying scheme of `T` with the restriction of the structure sheaf of
the big site along `AlgebraicGeometry.BigFppfOver.openSubFunctor`: over an open `V` it is
`AlgebraicGeometry.Scheme.Opens.topIso`, the functions on `V` being the global functions of the
open subscheme.  Naturality is the naturality of `AlgebraicGeometry.Scheme.restrictFunctorΓ`. -/
public noncomputable def openSubStructureMap (T : BigFppfOver B S hS) :
    T.left.obj.ringCatSheaf.obj ⟶
      (openSubFunctor B S hS T).op ⋙ (structureSheaf B S hS).obj where
  app V := (forget₂ CommRingCat.{u} RingCat.{u}).map
    (Scheme.Opens.topIso (X := T.left.obj) V.unop).inv
  naturality {V V'} h := by
    have key : T.left.obj.presheaf.map h ≫ (Scheme.Opens.topIso V'.unop).inv =
        (Scheme.Opens.topIso V.unop).inv ≫
          (T.left.obj.homOfLE (leOfHom h.unop)).appTop := by
      simp only [Scheme.Opens.topIso_inv, Scheme.homOfLE_appTop]
      refine Eq.trans (T.left.obj.presheaf.map_comp _ _).symm
        (Eq.trans ?_ (T.left.obj.presheaf.map_comp _ _))
      exact congrArg T.left.obj.presheaf.map (Subsingleton.elim _ _)
    exact (((forget₂ CommRingCat.{u} RingCat.{u}).map_comp _ _).symm.trans
      (congrArg ((forget₂ CommRingCat.{u} RingCat.{u}).map) key)).trans
      ((forget₂ CommRingCat.{u} RingCat.{u}).map_comp _ _)

/-- An open of the underlying scheme of `T` lying over an open `U` of `S` gives an object of the
big site whose structure morphism has range inside `U`. -/
public theorem range_openSubObj_hom_subset (T : BigFppfOver B S hS) {V : T.left.obj.Opens}
    {U : S.Opens} (hVU : V ≤ T.hom.hom ⁻¹ᵁ U) :
    Set.range ⇑(openSubObj B S hS T V).hom.hom ⊆ (U : Set S) := by
  rintro z ⟨w, rfl⟩
  exact hVU w.2

/-- **The source of the transpose.**  The pullback presheaf of the big site, read as a presheaf of
modules on the small Zariski site of the underlying scheme of `T` along
`AlgebraicGeometry.BigFppfOver.openSubFunctor` and
`AlgebraicGeometry.BigFppfOver.openSubStructureMap`. -/
public noncomputable abbrev openSubPullbackPresheaf (F : S.Modules)
    (T : BigFppfOver B S hS) :
    PresheafOfModules.{u} T.left.obj.ringCatSheaf.obj :=
  (PresheafOfModules.pushforward.{u} (openSubStructureMap B S hS T)).obj
    (presheafPullback B S hS F)

/-- The unique factoring of the open subscheme over an open `U` of `S` through `U`. -/
public noncomputable abbrev openSubPreimageHom (T : BigFppfOver B S hS) (U : S.Opens) :
    openSubObj B S hS T (T.hom.hom ⁻¹ᵁ U) ⟶ (opensToBig B S hS).obj U :=
  homOfRangeLe B S hS U
    (range_openSubObj_hom_subset B S hS T (le_refl (T.hom.hom ⁻¹ᵁ U)))

/-- **Restricting a function on `U` to the global functions of an open subscheme lying over
`U`.**  The structure morphism of `openSubObj T V` is `V.ι ≫ T.hom`, so
`AlgebraicGeometry.Scheme.Hom.appLE` of it, for the pair `(U, ⊤)`, is the restriction along the
structure morphism of `T` followed by `AlgebraicGeometry.Scheme.Opens.topIso`.  This is
`AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE` together with
`AlgebraicGeometry.Scheme.Opens.ι_appLE_top`. -/
public theorem openSubObj_appLE_top (T : BigFppfOver B S hS) {U : S.Opens}
    {V : T.left.obj.Opens} (hVU : V ≤ T.hom.hom ⁻¹ᵁ U)
    (hX : (⊤ : ((toScheme B S hS).obj (openSubObj B S hS T V)).Opens) ≤
      (openSubObj B S hS T V).hom.hom ⁻¹ᵁ U) :
    (openSubObj B S hS T V).hom.hom.appLE U ⊤ hX =
      T.hom.hom.appLE U V hVU ≫ (Scheme.Opens.topIso V).inv := by
  rw [← Scheme.Opens.ι_appLE_top V (Scheme.Opens.top_le_ι_preimage le_rfl)]
  exact (Scheme.Hom.appLE_comp_appLE V.ι T.hom.hom U V ⊤ hVU
    (Scheme.Opens.top_le_ι_preimage le_rfl)).symm

/-- **The scalars along which the transpose datum is semilinear.**  Over an open `U` of `S`, the
scalar by which `AlgebraicGeometry.BigFppfOver.presheafPullbackGenerator_smul` scales the generator
at `openSubObj T (T.hom⁻¹U)` is the image of the scalar under
`AlgebraicGeometry.BigFppfOver.openSubStructureMap` composed with the structure-sheaf map of the
structure morphism of `T` — which is exactly the scalar of the module structure of
`AlgebraicGeometry.BigFppfOver.openSubPullbackPresheaf` pushed forward along that morphism. -/
public theorem structureSheaf_map_openSubPreimageHom (T : BigFppfOver B S hS) (U : S.Opens)
    (hX : (⊤ : ((toScheme B S hS).obj
        (openSubObj B S hS T (T.hom.hom ⁻¹ᵁ U))).Opens) ≤
      (openSubObj B S hS T (T.hom.hom ⁻¹ᵁ U)).hom.hom ⁻¹ᵁ U)
    (r : Γ(S, U)) :
    (structureSheaf B S hS).obj.map (openSubPreimageHom B S hS T U).op
        ((structureMap B S hS).hom.app (op U) r) =
      (Scheme.Opens.topIso (T.hom.hom ⁻¹ᵁ U)).inv (T.hom.hom.app U r) := by
  refine Eq.trans (structureSheaf_map_structureMap_app B S hS
    (openSubPreimageHom B S hS T U) hX r) ?_
  refine Eq.trans (ConcreteCategory.congr_hom
    (openSubObj_appLE_top B S hS T (le_refl (T.hom.hom ⁻¹ᵁ U)) hX) r) ?_
  refine Eq.trans (CommRingCat.comp_apply _ _ r) ?_
  exact congrArg (fun z => (Scheme.Opens.topIso (T.hom.hom ⁻¹ᵁ U)).inv z)
    (ConcreteCategory.congr_hom (Scheme.Hom.appLE_eq_app T.hom.hom) r)

/-- **The transpose datum.**  Over an open `U` of `S`, the map carrying a section `a` of `F` to
the generator `AlgebraicGeometry.BigFppfOver.presheafPullbackGenerator` at the object
`openSubObj T (T.hom⁻¹U)` of the big site.  Its transpose across
`CategoryTheory.PresheafOfModules.pullbackPushforwardAdjunction` is
`AlgebraicGeometry.BigFppfOver.openSubBeta`.

Additivity is additivity of the unit and of restriction; semilinearity is
`AlgebraicGeometry.BigFppfOver.presheafPullbackGenerator_smul` rewritten by
`AlgebraicGeometry.BigFppfOver.structureSheaf_map_openSubPreimageHom`; and naturality is
`AlgebraicGeometry.BigFppfOver.presheafPullbackGenerator_map` followed by
`AlgebraicGeometry.BigFppfOver.presheafPullbackGenerator_map_le`. -/
public noncomputable def openSubUnit (F : S.Modules) (T : BigFppfOver B S hS) :
    (SheafOfModules.forget S.ringCatSheaf).obj F ⟶
      (PresheafOfModules.pushforward.{u} T.hom.hom.toRingCatSheafHom.hom).obj
        (openSubPullbackPresheaf B S hS F T) where
  app U := ModuleCat.homEquiv.symm
    { toFun := fun a => presheafPullbackGenerator B S hS F (openSubPreimageHom B S hS T U.unop) a
      map_add' := fun a b => Eq.trans
        (congrArg (fun z => (presheafPullback B S hS F).map
          (openSubPreimageHom B S hS T U.unop).op z)
          (map_add ((presheafPullbackUnit B S hS F).app (op U.unop)).hom a b))
        (map_add ((presheafPullback B S hS F).map
          (openSubPreimageHom B S hS T U.unop).op).hom _ _)
      map_smul' := fun r a => by
        have hX : (⊤ : ((toScheme B S hS).obj
            (openSubObj B S hS T (T.hom.hom ⁻¹ᵁ U.unop))).Opens) ≤
            (openSubObj B S hS T (T.hom.hom ⁻¹ᵁ U.unop)).hom.hom ⁻¹ᵁ U.unop :=
          fun w _ => range_openSubObj_hom_subset B S hS T
            (le_refl (T.hom.hom ⁻¹ᵁ U.unop)) ⟨w, rfl⟩
        refine Eq.trans (presheafPullbackGenerator_smul B S hS F
          (openSubPreimageHom B S hS T U.unop) r a) ?_
        refine Eq.trans (congrArg (fun c => c • presheafPullbackGenerator B S hS F
          (openSubPreimageHom B S hS T U.unop) a)
          (structureSheaf_map_openSubPreimageHom B S hS T U.unop hX r)) ?_
        rfl }
  naturality {U U'} h := by
    ext a
    have hle : (T.hom.hom ⁻¹ᵁ U'.unop) ≤ (T.hom.hom ⁻¹ᵁ U.unop) :=
      fun z hz => (leOfHom h.unop) hz
    have hmap : (presheafPullback B S hS F).map
          (openSubObjHom B S hS T hle).op
          (presheafPullbackGenerator B S hS F (openSubPreimageHom B S hS T U.unop) a) =
        presheafPullbackGenerator B S hS F (homOfRangeLe B S hS U.unop
          (range_openSubObj_hom_subset B S hS T (hle.trans (le_refl _)))) a :=
      presheafPullbackGenerator_map B S hS F (openSubObjHom B S hS T hle) _ _ a
    refine Eq.trans ?_ hmap.symm
    refine Eq.trans (congrArg (fun z => presheafPullbackGenerator B S hS F
      (openSubPreimageHom B S hS T U'.unop) z)
      (congrArg (fun k : U'.unop ⟶ U.unop =>
        ((SheafOfModules.forget S.ringCatSheaf).obj F).map k.op a)
        (Subsingleton.elim h.unop (homOfLE (leOfHom h.unop))))) ?_
    exact presheafPullbackGenerator_map_le B S hS F (leOfHom h.unop) _ _ a

/-- **The transpose `β`.**  The morphism of presheaves of modules, on the small Zariski site of
the underlying scheme of `T`, from the presheaf-level pullback of `F` along the structure morphism
of `T` to the big-site pullback presheaf read along
`AlgebraicGeometry.BigFppfOver.openSubFunctor`.  It is the transpose of
`AlgebraicGeometry.BigFppfOver.openSubUnit` across
`CategoryTheory.PresheafOfModules.pullbackPushforwardAdjunction`.

This is the map *out* of the presheaf-level pullback that local injectivity needs:
`CategoryTheory.PresheafOfModules.pullback` has no formula for its values, so a map out of it can
only come from the adjunction. -/
public noncomputable def openSubBeta (F : S.Modules) (T : BigFppfOver B S hS) :
    zariskiPullbackPresheaf T.hom.hom F ⟶ openSubPullbackPresheaf B S hS F T :=
  ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
    T.hom.hom.toRingCatSheafHom.hom).homEquiv _ _).symm (openSubUnit B S hS F T)

/-- `AlgebraicGeometry.BigFppfOver.openSubBeta` transposes back to
`AlgebraicGeometry.BigFppfOver.openSubUnit`. -/
public theorem unit_comp_map_openSubBeta (F : S.Modules)
    (T : BigFppfOver B S hS) :
    (PresheafOfModules.pullbackPushforwardAdjunction.{u}
          T.hom.hom.toRingCatSheafHom.hom).unit.app
        ((SheafOfModules.forget S.ringCatSheaf).obj F) ≫
        (PresheafOfModules.pushforward.{u} T.hom.hom.toRingCatSheafHom.hom).map
          (openSubBeta B S hS F T) =
      openSubUnit B S hS F T :=
  ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
      T.hom.hom.toRingCatSheafHom.hom).homEquiv_unit _ _ _).symm.trans
    (Equiv.apply_symm_apply _ _)

/-- **`β` on the image of the unit.**  `AlgebraicGeometry.BigFppfOver.unit_comp_map_openSubBeta`
evaluated at an open `U` of `S` and applied to a section. -/
public theorem openSubBeta_unit_app (F : S.Modules) (T : BigFppfOver B S hS) (U : S.Opens)
    (a : ((SheafOfModules.forget S.ringCatSheaf).obj F).obj (op U)) :
    (openSubBeta B S hS F T).app (op (T.hom.hom ⁻¹ᵁ U))
        (((PresheafOfModules.pullbackPushforwardAdjunction.{u}
          T.hom.hom.toRingCatSheafHom.hom).unit.app
            ((SheafOfModules.forget S.ringCatSheaf).obj F)).app (op U) a) =
      presheafPullbackGenerator B S hS F (openSubPreimageHom B S hS T U) a := by
  have h := unit_comp_map_openSubBeta B S hS F T
  have h2 := congrArg (fun k : (SheafOfModules.forget S.ringCatSheaf).obj F ⟶
      (PresheafOfModules.pushforward.{u} T.hom.hom.toRingCatSheafHom.hom).obj
        (openSubPullbackPresheaf B S hS F T) => PresheafOfModules.Hom.app k (op U)) h
  rw [PresheafOfModules.comp_app] at h2
  exact ConcreteCategory.congr_hom h2 a

/-- **`β` on a generator.**  Over an open `V` of the underlying scheme of `T` lying over an open
`U` of `S`, `AlgebraicGeometry.BigFppfOver.openSubBeta` carries the restriction to `V` of the
image under the unit of a section `a` of `F` over `U` to the generator
`AlgebraicGeometry.BigFppfOver.presheafPullbackGenerator` at the object `openSubObj T V`.

Compare `AlgebraicGeometry.zariskiPullbackToSheaf_generator`, which evaluates the sheafification
map on the same element: the two together are what the argument below compares. -/
public theorem openSubBeta_generator (F : S.Modules) (T : BigFppfOver B S hS) (U : S.Opens)
    {V : T.left.obj.Opens} (hVU : V ≤ T.hom.hom ⁻¹ᵁ U)
    (a : ((SheafOfModules.forget S.ringCatSheaf).obj F).obj (op U)) :
    (openSubBeta B S hS F T).app (op V)
        ((zariskiPullbackPresheaf T.hom.hom F).map (homOfLE hVU).op
          (((PresheafOfModules.pullbackPushforwardAdjunction.{u}
            T.hom.hom.toRingCatSheafHom.hom).unit.app
              ((SheafOfModules.forget S.ringCatSheaf).obj F)).app (op U) a)) =
      presheafPullbackGenerator B S hS F
        (homOfRangeLe B S hS U (range_openSubObj_hom_subset B S hS T hVU)) a := by
  refine Eq.trans (PresheafOfModules.naturality_apply (openSubBeta B S hS F T)
    (homOfLE hVU).op _) ?_
  refine Eq.trans (congrArg (fun z => (openSubPullbackPresheaf B S hS F T).map
    (homOfLE hVU).op z) (openSubBeta_unit_app B S hS F T U a)) ?_
  exact presheafPullbackGenerator_map B S hS F (openSubObjHom B S hS T hVU) _ _ a

end BigFppfOver

end AlgebraicGeometry

end
