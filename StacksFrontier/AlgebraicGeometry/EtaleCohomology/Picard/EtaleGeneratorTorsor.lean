module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Picard.EtaleGeneratorSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsorClassRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.UniverseLiftTorsorClass

/-!
# The torsor of local generators of an invertible module, on sites over the small étale site

Let `L` be an invertible module on a scheme `S` and let `G : (C, J) ⥤ S_étale` be a continuous
and cocontinuous functor of sites, for instance the identity of Mathlib's small étale site, the
inclusion of a size-bounded small étale site (Tag 021B) or of a small model of it. Let `H` be an
abelian sheaf on `C` whose sections over `U` are identified, compatibly with restriction, with
the invertible global functions on `G U`: `𝐆_m` in any coefficient universe, the units of the
structure sheaf of a ringed site, or a universe lift of one of these.

`Stacks.EtaleGenerators.generatorTorsorOn` is the torsor under `H` whose sections over `U` are
the universal generators of `(G U)^*L` (`Stacks.EtaleGenerators.generatorPresheaf`).

All the identifications through which [Stacks, Tag 03P8] passes between `H¹` of the various
incarnations of `𝐆_m` — coefficient isomorphisms, universe lifts, restriction to a dense subsite
— carry the class of one of these torsors to the class of another one; the comparison maps of
torsors are the identity on generators.

## Main definitions

* `Stacks.EtaleGenerators.GlobalUnitsEquiv`: an identification of the sections of an abelian
  sheaf on `C` with the invertible global functions along `G`.
* `Stacks.EtaleGenerators.generatorTorsorOn`: the torsor of local generators.

## Main results

* `Stacks.EtaleGenerators.sheafHMap_generatorTorsorOn`: naturality in the coefficient sheaf.
* `Stacks.EtaleGenerators.sheafHOneAddEquiv_generatorTorsorOn`: the universe lift of `H¹`.
* `Stacks.EtaleGenerators.hAddEquiv_generatorTorsorOn`: restriction to a dense subsite.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry Stacks.Cohomology.Torsors

universe w w' s t v₁ u₁ v₂ u₂ u

namespace Stacks.EtaleGenerators

variable {S : Scheme.{u}} (L : S.Modules)
  (hL : Stacks.SheafOfModules.IsInvertible S.presheaf
    (Stacks.RingedSpace.structureRingSheaf S.toRingedSpace).property L)

section Constructor

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) (G : C ⥤ S.Etale)

/-- An identification of the sections of an abelian sheaf `H` on `C` with the invertible global
functions on the images under `G : C ⥤ S_étale`, compatible with restriction. -/
structure GlobalUnitsEquiv (H : Sheaf J AddCommGrpCat.{w}) where
  /-- The identification on sections over `U`. -/
  equiv (U : Cᵒᵖ) : H.obj.obj U ≃+ Additive (Γ((G.obj U.unop).left, ⊤))ˣ
  /-- Restriction of sections is pullback of global functions. -/
  naturality {U V : Cᵒᵖ} (f : U ⟶ V) (h : H.obj.obj U) :
    equiv V (H.obj.map f h) =
      Additive.ofMul (Units.map (G.map f.unop).left.appTop.hom (Additive.toMul (equiv U h)))

variable {J G} in
/-- The invertible global function attached to a section of `H`, read multiplicatively. -/
def GlobalUnitsEquiv.unitOf {H : Sheaf J AddCommGrpCat.{w}} (e : GlobalUnitsEquiv J G H)
    {U : Cᵒᵖ} (g : (abelianSheafAsGroupSheaf H).presheaf.obj U) :
    (Γ((G.obj U.unop).left, ⊤))ˣ :=
  Additive.toMul (e.equiv U (Multiplicative.toAdd g))

variable {J G} in
/-- `GlobalUnitsEquiv.unitOf` sends the identity section to the unit `1`. -/
theorem GlobalUnitsEquiv.unitOf_one {H : Sheaf J AddCommGrpCat.{w}} (e : GlobalUnitsEquiv J G H)
    (U : Cᵒᵖ) : e.unitOf (1 : (abelianSheafAsGroupSheaf H).presheaf.obj U) = 1 :=
  congrArg Additive.toMul (map_zero (e.equiv U))

variable {J G} in
/-- `GlobalUnitsEquiv.unitOf` is multiplicative. -/
theorem GlobalUnitsEquiv.unitOf_mul {H : Sheaf J AddCommGrpCat.{w}} (e : GlobalUnitsEquiv J G H)
    {U : Cᵒᵖ} (g h : (abelianSheafAsGroupSheaf H).presheaf.obj U) :
    e.unitOf (g * h) = e.unitOf g * e.unitOf h :=
  congrArg Additive.toMul (map_add (e.equiv U) (Multiplicative.toAdd g : H.obj.obj U)
    (Multiplicative.toAdd h : H.obj.obj U))

variable {J G} in
/-- `GlobalUnitsEquiv.unitOf` carries restriction of sections along `f` to pullback of invertible
global functions along `G.map f.unop`. -/
theorem GlobalUnitsEquiv.unitOf_map {H : Sheaf J AddCommGrpCat.{w}} (e : GlobalUnitsEquiv J G H)
    {U V : Cᵒᵖ} (f : U ⟶ V) (g : (abelianSheafAsGroupSheaf H).presheaf.obj U) :
    e.unitOf ((abelianSheafAsGroupSheaf H).presheaf.map f g) =
      Units.map (G.map f.unop).left.appTop.hom (e.unitOf g) :=
  congrArg Additive.toMul (e.naturality f (Multiplicative.toAdd g))

variable {J G} in
/-- On the sections over each object `U`, `GlobalUnitsEquiv.unitOf` is a bijection. -/
theorem GlobalUnitsEquiv.unitOf_bijective {H : Sheaf J AddCommGrpCat.{w}}
    (e : GlobalUnitsEquiv J G H) (U : Cᵒᵖ) :
    Function.Bijective (e.unitOf (U := U)) :=
  Additive.toMul.bijective.comp ((e.equiv U).bijective.comp Multiplicative.toAdd.bijective)

variable [G.IsContinuous J S.smallEtaleTopology] [G.IsCocontinuous J S.smallEtaleTopology]

/-- The universal generators of `(G U)^*L` over the objects `U` of `C`, with sections raised to
the universe `max u t`. -/
abbrev liftedGeneratorPresheaf.{t', u', u₁', v₁'} {S : Scheme.{u'}} (L : S.Modules) {C : Type u₁'}
    [Category.{v₁'} C] (G : C ⥤ S.Etale) : Cᵒᵖ ⥤ Type (max u' t') where
  obj U := ULift.{t'} ((generatorPresheaf L).obj (op (G.obj U.unop)))
  map f := TypeCat.ofHom fun x => ULift.up ((generatorPresheaf L).map (G.map f.unop).op x.down)
  map_id U := by
    ext x
    change (generatorPresheaf L).map (G.map (𝟙 U.unop)).op x.down = x.down
    rw [G.map_id, op_id, Functor.map_id_apply]
  map_comp f g := by
    ext x
    change (generatorPresheaf L).map (G.map (f ≫ g).unop).op x.down =
      (generatorPresheaf L).map (G.map g.unop).op
        ((generatorPresheaf L).map (G.map f.unop).op x.down)
    rw [unop_comp, G.map_comp, op_comp, Functor.map_comp_apply]

/-- Restriction in `liftedGeneratorPresheaf` is restriction in `generatorPresheaf` along `G`. -/
theorem liftedGeneratorPresheaf_map_down {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : (liftedGeneratorPresheaf.{t} L G).obj U) :
    ((liftedGeneratorPresheaf.{t} L G).map f x).down =
      (generatorPresheaf L).map (G.map f.unop).op x.down :=
  rfl

omit [G.IsContinuous J S.smallEtaleTopology] [G.IsCocontinuous J S.smallEtaleTopology] in
/-- Restriction in `liftedGeneratorPresheaf` commutes with the action of the units
`GlobalUnitsEquiv.unitOf e g`. -/
theorem liftedGeneratorPresheaf_map_unitSmul {H : Sheaf J AddCommGrpCat.{w}}
    (e : GlobalUnitsEquiv J G H) {U V : Cᵒᵖ} (f : U ⟶ V)
    (g : (abelianSheafAsGroupSheaf H).presheaf.obj U)
    (s : (liftedGeneratorPresheaf.{t} L G).obj U) :
    (liftedGeneratorPresheaf.{t} L G).map f (ULift.up (unitSmul L (e.unitOf g) s.down)) =
      ULift.up (unitSmul L (e.unitOf ((abelianSheafAsGroupSheaf H).presheaf.map f g))
        ((liftedGeneratorPresheaf.{t} L G).map f s).down) := by
  apply ULift.ext
  rw [liftedGeneratorPresheaf_map_down, liftedGeneratorPresheaf_map_down, map_unitSmul,
    e.unitOf_map]

include hL in
omit [G.IsCocontinuous J S.smallEtaleTopology] in
/-- For `L` invertible, `liftedGeneratorPresheaf L G` is a sheaf for `J`. -/
theorem isSheaf_liftedGeneratorPresheaf :
    Presheaf.IsSheaf J (liftedGeneratorPresheaf.{t} L G) :=
  (Presheaf.isSheaf_of_iso_iff (NatIso.ofComponents (fun _ => Iso.refl _) fun _ => rfl)).1
    ((isSheaf_iff_isSheaf_of_type _ _).2
      (G.op_comp_isSheaf_of_isSheaf_type J (Presieve.isSheaf_comp_uliftFunctor _
        ((isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_generatorPresheaf L hL)))))

variable {J G} in
/-- The pseudo-torsor of local generators under `H`. -/
def generatorPseudoTorsorOn {H : Sheaf J AddCommGrpCat.{max u t}} (e : GlobalUnitsEquiv J G H) :
    PseudoTorsor.{max u t} (abelianSheafAsGroupSheaf H) where
  presheaf := liftedGeneratorPresheaf.{t} L G
  isSheaf := isSheaf_liftedGeneratorPresheaf L hL J G
  act U g s := ULift.up (unitSmul L (e.unitOf g) s.down)
  one_act U s := by
    refine ULift.ext (Subtype.ext ?_)
    change sec L (unitSmul L (e.unitOf 1) s.down) = sec L s.down
    rw [sec_unitSmul, e.unitOf_one, Units.val_one, one_smul]
  mul_act U g h s := by
    refine ULift.ext (Subtype.ext ?_)
    change sec L (unitSmul L (e.unitOf (g * h)) s.down) =
      sec L (unitSmul L (e.unitOf g) (unitSmul L (e.unitOf h) s.down))
    rw [sec_unitSmul, sec_unitSmul, sec_unitSmul, e.unitOf_mul, Units.val_mul, mul_smul]
  naturality {U V} f g s := liftedGeneratorPresheaf_map_unitSmul L J G e f g s
  simplyTransitive U _ s t := by
    obtain ⟨a, ha, hu⟩ := Stacks.Cohomology.Generators.generators_unique_unit (sec L s.down)
      (sec L t.down) (IsUniversalGenerator.bijective L s.down.2)
      (IsUniversalGenerator.bijective L t.down.2)
    obtain ⟨g, rfl⟩ := (e.unitOf_bijective U).2 a
    refine ⟨g, ULift.ext (Subtype.ext ((sec_unitSmul L _ _).trans ha)), fun g' hg' => ?_⟩
    refine (e.unitOf_bijective U).1 (hu _ ?_)
    exact (sec_unitSmul L _ _).symm.trans (congrArg (fun z => sec L z.down) hg')

variable {J G} in
/-- **The torsor of local generators of `L` under `H`.** Its sections over `U` are the
universal generators of `(G U)^*L`, a unit acting by multiplication. -/
def generatorTorsorOn {H : Sheaf J AddCommGrpCat.{max u t}} (e : GlobalUnitsEquiv J G H) :
    AbelianTorsor H :=
  ⟨generatorPseudoTorsorOn L hL e, fun U => by
    obtain ⟨R, hR, hne⟩ := exists_covering_nonempty_generatorPresheaf L hL (G.obj U)
    exact ⟨R.functorPullback G, G.cover_lift J S.smallEtaleTopology hR,
      fun V f hf => (hne hf).elim fun s => ⟨(ULift.up s : ULift.{t} _)⟩⟩⟩

/-- A section `g` of `H` acts on a generator by multiplication with the unit
`GlobalUnitsEquiv.unitOf e g`. -/
theorem generatorTorsorOn_act {H : Sheaf J AddCommGrpCat.{max u t}} (e : GlobalUnitsEquiv J G H)
    (U : Cᵒᵖ) (g : (abelianSheafAsGroupSheaf H).presheaf.obj U)
    (x : (generatorTorsorOn.{t} L hL e).1.presheaf.obj U) :
    (generatorTorsorOn.{t} L hL e).1.act U g x = ULift.up (unitSmul L (e.unitOf g) x.down) :=
  rfl

/-! ### The class of the torsor of generators under the identifications of `H¹` -/

section Classes

variable {J G}

/-- **Naturality in the coefficient sheaf.** A morphism of coefficient sheaves compatible with
the identifications with the global units carries the class of the torsor of generators to the
class of the torsor of generators. -/
theorem sheafHMap_generatorTorsorOn [HasSheafify J AddCommGrpCat.{max u t}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{max u t})] {H H' : Sheaf J AddCommGrpCat.{max u t}}
    (φ : H ⟶ H') (e : GlobalUnitsEquiv J G H) (e' : GlobalUnitsEquiv J G H')
    (he : ∀ (U : Cᵒᵖ) (h : H.obj.obj U), e'.equiv U (φ.hom.app U h) = e.equiv U h) :
    Sheaf.H.map φ 1 (torsorIsoClassesEquivH1 H (Quotient.mk _ (generatorTorsorOn.{t} L hL e))) =
      torsorIsoClassesEquivH1 H' (Quotient.mk _ (generatorTorsorOn.{t} L hL e')) :=
  torsorIsoClassesEquivH1_naturality φ _ _ (𝟙 _) fun U h x =>
    congrArg (fun a => ULift.up (unitSmul L a x.down))
      (congrArg Additive.toMul (he U h)).symm

/-- **The universe lift of `H¹`.** `Stacks.Sheaves.UniverseLift.sheafHOneAddEquiv` carries the
class of the torsor of generators under `H` to the class of the torsor of generators under the
universe lift of `H`. -/
theorem sheafHOneAddEquiv_generatorTorsorOn
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u t}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u t s}]
    [HasSheafify J AddCommGrpCat.{max u t}] [HasSheafify J AddCommGrpCat.{max u t s}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{max u t})]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{max u t s})]
    (H : Sheaf J AddCommGrpCat.{max u t}) (e : GlobalUnitsEquiv J G H)
    (e' : GlobalUnitsEquiv J G
      ((Stacks.Sheaves.UniverseLift.uliftSheafFunctor.{s, max u t} J).obj H))
    (he : ∀ (U : Cᵒᵖ) (h : H.obj.obj U), e'.equiv U (ULift.up h) = e.equiv U h) :
    Stacks.Sheaves.UniverseLift.sheafHOneAddEquiv.{w, w', s, max u t} J H
        (torsorIsoClassesEquivH1 H (Quotient.mk _ (generatorTorsorOn.{t} L hL e))) =
      torsorIsoClassesEquivH1 _ (Quotient.mk _ (generatorTorsorOn.{max t s} L hL e')) := by
  refine sheafHOneAddEquiv_torsorClass J H _ _
    { app U := TypeCat.ofHom fun x => ULift.up (ULift.up x.down)
      naturality _ _ _ := rfl } (fun U => ⟨fun x y h => ?_, fun y => ⟨ULift.up y.down.down, rfl⟩⟩)
    (fun U h x => ?_)
  · exact ULift.ext (congrArg (fun z => z.down.down) h)
  · show ULift.up (ULift.up (unitSmul L (e'.unitOf _) x.down)) =
      ULift.up (ULift.up (unitSmul L (e.unitOf _) x.down))
    exact congrArg (fun a => ULift.up (ULift.up (unitSmul L a x.down)))
      (congrArg Additive.toMul (he U h))

/-- **Restriction to a dense subsite.** The dense-subsite comparison of `H¹` (Tag 00XU) carries
the class of the torsor of generators under `H` to the class of the torsor of generators under
the restriction of `H`. -/
theorem hAddEquiv_generatorTorsorOn {C' : Type u₂} [Category.{v₂} C']
    (J' : GrothendieckTopology C') (F : C' ⥤ C) [F.IsDenseSubsite J' J]
    [HasSheafify J' AddCommGrpCat.{max u t}] [HasSheafify J AddCommGrpCat.{max u t}]
    [(F.sheafPushforwardContinuous AddCommGrpCat.{max u t} J' J).IsEquivalence]
    [HasExt.{w} (Sheaf J' AddCommGrpCat.{max u t})] [HasExt.{w} (Sheaf J AddCommGrpCat.{max u t})]
    [EnoughInjectives (Sheaf J' AddCommGrpCat.{max u t})]
    [(F ⋙ G).IsContinuous J' S.smallEtaleTopology] [(F ⋙ G).IsCocontinuous J' S.smallEtaleTopology]
    (H : Sheaf J AddCommGrpCat.{max u t}) (e : GlobalUnitsEquiv J G H)
    (e' : GlobalUnitsEquiv J' (F ⋙ G) ((F.sheafPushforwardContinuous _ J' J).obj H))
    (he : ∀ (U : C'ᵒᵖ) (h : H.obj.obj (F.op.obj U)), e'.equiv U h = e.equiv (F.op.obj U) h) :
    Stacks.Cohomology.DenseSubsite.hAddEquiv J' J F H 1
        (torsorIsoClassesEquivH1 H (Quotient.mk _ (generatorTorsorOn.{t} L hL e))) =
      torsorIsoClassesEquivH1 _ (Quotient.mk _ (generatorTorsorOn.{t} L hL e')) := by
  refine hAddEquiv_torsorClass J' J F H _ _
    { app U := TypeCat.ofHom fun x => x
      naturality _ _ _ := rfl } (fun U => Function.bijective_id) (fun U h x => ?_)
  exact congrArg (fun a => ULift.up (unitSmul L a x.down)) (congrArg Additive.toMul (he U h))

end Classes

end Constructor

end Stacks.EtaleGenerators

end
