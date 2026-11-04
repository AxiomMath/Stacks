module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.QuasiCoherentPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleFinalPullbackUnitIdentity

/-!
# The presheaf `(f : T → S) ↦ Γ(T, f_small^*𝓖)` on a big site over `S`

Let `B` be a big étale site, `S` a scheme it contains and `𝓖` an arbitrary sheaf of
`𝒪`-modules on the small étale site `S_étale`.  For an object `f : T → S` of the big category
`(Sch/S)` the inverse image `f_small^*𝓖` along the morphism of ringed sites
`ε_f : T_étale ⟶ S_étale` of **Stacks 070R (2)** is a sheaf of `𝒪`-modules on `T_étale`, and
this file assembles its global sections into a presheaf of abelian groups on `(Sch/S)`:

`AlgebraicGeometry.SmallEtale.sectionsSheafTauPresheaf`.

This is the presheaf **Stacks 070S part (3)** compares `(id_{τ,étale})^*𝓖` with.

## The restriction maps

Nothing computes the sections of a left adjoint, so the restriction map along a morphism
`g : T' → T` of `(Sch/S)` is the one the adjunction supplies:
`AlgebraicGeometry.SmallEtale.finalPullbackUnit` for `g`, followed by the composition law
`AlgebraicGeometry.SmallEtale.smallEtalePullbackFactoredCompIso` for the factorization
`g ≫ f = f'` read on sections.  That this is functorial is exactly the pair of laws
`AlgebraicGeometry.SmallEtale.finalPullbackUnit_factoredComp_id` and
`AlgebraicGeometry.SmallEtale.finalPullbackUnit_factoredComp`, the second combined with the
cocycle `AlgebraicGeometry.SmallEtale.smallEtalePullbackFactoredCompIso_assoc` of
**Stacks 021J** at the level of modules.

## The localization map

Over an *étale* `V / S` the sections rule can be compared with `𝓖` itself: the unit along
`ε_v` read on sections over `V` lands in `Γ(V ×_S V, v_small^*𝓖)`, and restriction along the
diagonal `V → V ×_S V` — `AlgebraicGeometry.SmallEtale.finalToSelfBaseChange` — brings it to
`Γ(V, v_small^*𝓖)`, which is the value of the sections rule at `V / S`.  That this is natural
in `V` is `AlgebraicGeometry.SmallEtale.sectionsSheafTauLocApp_naturality`; the two units
involved are for *different* morphisms, so what brings them into contact is the unit law of
Stacks 070R (2) over an arbitrary object,
`AlgebraicGeometry.SmallEtale.unitSectionsApp_factoredComp_obj`, together with the naturality
of the diagonal, `AlgebraicGeometry.SmallEtale.finalToSelfBaseChange_naturality`.  The latter
is the only geometric input, and it holds for the only available reason: both sides are
morphisms into a base change, so
`AlgebraicGeometry.SmallEtale.hom_ext_of_comp_fst_smallEtaleBaseChange` reduces it to the
projection upstairs, where the two projection identities of Stacks 021J carry both routes to
the underlying morphism of `k`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.sectionsSheafTauObj` and
  `AlgebraicGeometry.SmallEtale.sectionsSheafTauMap`: the sections `Γ(T, f_small^*𝓖)` and the
  restriction maps between them.
* `AlgebraicGeometry.SmallEtale.sectionsSheafTauPresheaf` and
  `AlgebraicGeometry.SmallEtale.sectionsSheafTauPresheafOfModules`: the presheaf of abelian
  groups and the presheaf of `𝒪`-modules.
* `AlgebraicGeometry.SmallEtale.finalToSelfBaseChange`: the diagonal arrow.
* `AlgebraicGeometry.SmallEtale.sectionsSheafTauLocApp`: the localization map on sections over
  an étale `V / S`.

## Main results

* `AlgebraicGeometry.SmallEtale.finalToSelfBaseChange_naturality`: **the diagonal is natural**,
  in the form the localization map needs.
* `AlgebraicGeometry.SmallEtale.unitSectionsApp_factoredComp_obj`: the unit law of
  Stacks 070R (2) on sections over an arbitrary object.
* `AlgebraicGeometry.SmallEtale.sectionsSheafTauLocApp_naturality` and
  `AlgebraicGeometry.SmallEtale.sectionsSheafTauLocApp_smul`: the localization map is natural
  and linear.
* `AlgebraicGeometry.SmallEtale.sectionsSheafTauRho` and
  `AlgebraicGeometry.SmallEtale.sectionsSheafTauRho_naturality`: the comparison of the sections
  rule at `W / S` with the sections of `f_small^*𝓖` at `W`, for `W` in the small étale site of
  the scheme of `T / S`, and its naturality in `W`.  Its proof is structurally the proof of
  `sectionsSheafTauMap_comp`: what is left after cancelling the localization map and the
  pullback unit is the cocycle of Stacks 021J.
* `AlgebraicGeometry.SmallEtale.smallEtaleToBigOver`,
  `AlgebraicGeometry.SmallEtale.smallEtaleToBigOverRingMap` and
  `AlgebraicGeometry.SmallEtale.nuProj`: the functor presenting `i_T` of Stacks 021F, the
  identity `i_T^{-1}𝒪 = 𝒪` — which is `𝟙`, no comparison map — and the projection
  `T ×_S V / S ⟶ V / S` of Stacks 021I (4), natural in `V`.
* `AlgebraicGeometry.SmallEtale.sectionsSheafTauMap_eq_rho`: **the restriction maps of the
  sections rule along an étale `W → T` are the restriction maps of `f_small^*𝓖` itself**,
  followed by `AlgebraicGeometry.SmallEtale.sectionsSheafTauRho`.  This is what makes the local
  bijectivity of the comparison of Stacks 070S part (3) at an object `T` reduce to local
  bijectivity of the sheafification unit on the small étale site of `T`: the sections of the
  rule at `T` and the global sections of `f_small^*𝓖` are *the same group by definition*, so
  no transport along a comparison at the final object is needed.
* `AlgebraicGeometry.SmallEtale.sectionsSheafTauRho_final` and
  `AlgebraicGeometry.SmallEtale.sectionsSheafTauRho_app_final`: **at the final object `ρ'` is the
  identity**, respectively restriction along the canonical isomorphism `i_T(T/T) ≅ T`.  This is
  why the factorization is an argument of `sectionsSheafTauRho` rather than being taken to be
  `w ≫ f`.
* `AlgebraicGeometry.SmallEtale.sectionsSheafTauRho_unitSectionsApp`: **the generator identity**
  of Stacks 070S part (3) — on the image under the unit along `ε_f` of a section of `𝓖` over an
  étale `V / S`, `ρ'` at `T ×_S V` is the localization map at `V` followed by restriction along
  the projection `T ×_S V / S ⟶ V / S` of Stacks 021I (4).  Both sides are a two-step unit
  followed by a restriction, and
  `AlgebraicGeometry.SmallEtale.unitSectionsApp_factoredComp_obj_comp` contracts each into the
  one-step unit along `T ×_S V → S`; what is left is
  `AlgebraicGeometry.SmallEtale.finalToSelfBaseChange_comp_factoredCompIso_eq`.
* `AlgebraicGeometry.SmallEtale.sectionsSheafTauTheta_eq`, and with it
  `AlgebraicGeometry.SmallEtale.isLocallySurjective_sectionsSheafTauTheta` and
  `AlgebraicGeometry.SmallEtale.isLocallyInjective_sectionsSheafTauTheta`: **the comparison `θ`
  from the presheaf-level inverse image of `𝓖` along `ε_f` to `f_small^*𝓖` is the sheafification
  unit followed by an isomorphism**, hence locally bijective.  The isomorphism is
  `CategoryTheory.SheafOfModules.pullbackIso`, pinned down by its effect on units.
* `AlgebraicGeometry.SmallEtale.kappaLift` and
  `AlgebraicGeometry.SmallEtale.kappaLift_spec`: the bijection `Hom_S(W, V) ≅ Hom_T(W, T ×_S V)`
  in the direction the surjectivity of `κ` consumes.

The comparison of Stacks 070S part (3) itself, and its local bijectivity, are in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleSectionsSheafTauBigSite.lean`.

## References

* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)

## Implementation notes

The sections rule is declared with values in `Ab` rather than in `AddCommGrpCat`.  The two are
the same category, but the restriction maps of a presheaf of modules and the sections of a
morphism of sheaves of modules are both spelled at `Ab`, and a chain mixing the two spellings
is one at which `CategoryTheory.Category.assoc` does not *rewrite* — `rw` reports its own
pattern as missing — so `slice` and every associativity-normalising tactic silently fail.
Declaring the rule at `Ab` removes the mixture.  Where a chain still has to be re-associated
across the remaining boundary, it is done in *term* mode, where associativity is applied as a
term and has only to typecheck.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Base change along a morphism to the base object of the big étale category over `S` is
continuous, restated in the spelling instance search meets below: the source site is the small
étale site of `B.obj S hS`, whose carrier is `(B.obj S hS).obj` rather than `S`. -/
public instance isContinuous_smallEtaleBaseChange_toBase {X : B.Scheme}
    (a : X ⟶ B.obj S hS) :
    Functor.IsContinuous (smallEtaleBaseChange B a)
      (topology B (B.obj S hS).obj (B.obj S hS).property)
      (topology B X.obj X.property) :=
  smallEtaleBaseChange_isContinuous B a

variable (𝓖 : SheafOfModules.{u} (structureSheaf B S hS))

/-- The inverse image `f_small^*𝓖` of `𝓖` along the morphism of ringed sites `ε_f` of
Stacks 070R (2), for an object `f : T → S` of the big étale category over `S`. -/
public abbrev sectionsSheafTauPullback (T : BigEtaleOver B S hS) :
    SheafOfModules.{u} (structureSheaf B T.left.obj T.left.property) :=
  (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B T.hom)).obj 𝓖

/-- `Γ(T, f_small^*𝓖)`, the sections of the inverse image over the final object of
`T_étale`. -/
public abbrev sectionsSheafTauObj (T : BigEtaleOver B S hS) : Ab.{u} :=
  (sectionsSheafTauPullback B S hS 𝓖 T).val.presheaf.obj
    (op (final B T.left.obj T.left.property))

/-- The restriction map of the sections rule along a morphism `g : T' ⟶ T` of the big étale
category over `S`: pulling a section over the final object back along `g`, read through the
composition law of Stacks 070R (2) for the factorization `g ≫ f = f'`. -/
public def sectionsSheafTauMap {T T' : BigEtaleOver B S hS} (g : T' ⟶ T) :
    sectionsSheafTauObj B S hS 𝓖 T ⟶ sectionsSheafTauObj B S hS 𝓖 T' :=
  finalPullbackUnit B g.left (sectionsSheafTauPullback B S hS 𝓖 T) ≫
    smallEtaleSectionsApp B
      ((smallEtalePullbackFactoredCompIso B g.left T.hom T'.hom (Over.w g)).hom.app 𝓖)
      (final B T'.left.obj T'.left.property)

/-- The sections rule takes an identity to the identity: this is
`AlgebraicGeometry.SmallEtale.finalPullbackUnit_factoredComp_id`. -/
public theorem sectionsSheafTauMap_id (T : BigEtaleOver B S hS) :
    sectionsSheafTauMap B S hS 𝓖 (𝟙 T) = 𝟙 _ :=
  finalPullbackUnit_factoredComp_id B T.left T.hom 𝓖

/-- The cocycle of Stacks 021J for the composition law, read on sections over the final object
and combined with naturality of `finalPullbackUnit` in the module: the step shared by
`AlgebraicGeometry.SmallEtale.sectionsSheafTauMap_comp` and
`AlgebraicGeometry.SmallEtale.sectionsSheafTauRho_naturality`. -/
private theorem sectionsApp_pullbackUnit_cocycle {X Y Z : B.Scheme} (a : X ⟶ Y) (b : Y ⟶ Z)
    (c : Z ⟶ B.obj S hS) (bc : Y ⟶ B.obj S hS) (hbc : b ≫ c = bc) (ab : X ⟶ Z)
    (hab : a ≫ b = ab) (abc : X ⟶ B.obj S hS) (habc : a ≫ bc = abc) (habc' : ab ≫ c = abc) :
    smallEtaleSectionsApp B ((smallEtalePullbackFactoredCompIso B b c bc hbc).hom.app 𝓖)
          (final B Y.obj Y.property) ≫
        finalPullbackUnit B a ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B bc)).obj
          𝓖) ≫
          smallEtaleSectionsApp B ((smallEtalePullbackFactoredCompIso B a bc abc habc).hom.app 𝓖)
            (final B X.obj X.property) =
      finalPullbackUnit B a ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B b)).obj
          ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B c)).obj 𝓖)) ≫
        smallEtaleSectionsApp B ((smallEtalePullbackFactoredCompIso B a b ab hab).hom.app
          ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B c)).obj 𝓖))
          (final B X.obj X.property) ≫
        smallEtaleSectionsApp B ((smallEtalePullbackFactoredCompIso B ab c abc habc').hom.app 𝓖)
          (final B X.obj X.property) := by
  have hcoc := congrArg (fun t : (_ : _ ⥤ _) ≅ _ => t.hom.app 𝓖)
    (smallEtalePullbackFactoredCompIso_assoc B a b c bc hbc ab hab abc habc habc')
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp] at hcoc
  have hstep := congrArg (fun φ => smallEtaleSectionsApp B φ (final B X.obj X.property)) hcoc
  simp only [smallEtaleSectionsApp_comp] at hstep
  rw [← Category.assoc, finalPullbackUnit_naturality B a, Category.assoc, ← hstep]
  rfl

/-- The sections rule is compatible with composition.  The two inputs are
`AlgebraicGeometry.SmallEtale.finalPullbackUnit_factoredComp`, which contracts the two
pullback units, and the cocycle
`AlgebraicGeometry.SmallEtale.smallEtalePullbackFactoredCompIso_assoc` of Stacks 021J, which
contracts the two comparisons; naturality of `finalPullbackUnit` in the module is what brings
them into contact. -/
public theorem sectionsSheafTauMap_comp {T T' T'' : BigEtaleOver B S hS}
    (g : T' ⟶ T) (g' : T'' ⟶ T') :
    sectionsSheafTauMap B S hS 𝓖 (g' ≫ g) =
      sectionsSheafTauMap B S hS 𝓖 g ≫ sectionsSheafTauMap B S hS 𝓖 g' := by
  have hfc := finalPullbackUnit_factoredComp B g'.left g.left (g' ≫ g).left rfl
    (sectionsSheafTauPullback B S hS 𝓖 T)
  simp only [sectionsSheafTauMap, Category.assoc]
  slice_rhs 2 4 => rw [sectionsApp_pullbackUnit_cocycle B S hS 𝓖 g'.left g.left T.hom T'.hom
    (Over.w g) (g' ≫ g).left rfl T''.hom (Over.w g') (Over.w (g' ≫ g))]
  slice_rhs 1 3 => rw [hfc]

/-- **The sections rule `(f : T → S) ↦ Γ(T, f_small^*𝓖)` as a presheaf of abelian groups** on
the big étale category over `S`. -/
public def sectionsSheafTauPresheaf : (BigEtaleOver B S hS)ᵒᵖ ⥤ Ab.{u} where
  obj T := sectionsSheafTauObj B S hS 𝓖 T.unop
  map g := sectionsSheafTauMap B S hS 𝓖 g.unop
  map_id T := sectionsSheafTauMap_id B S hS 𝓖 T.unop
  map_comp g g' := sectionsSheafTauMap_comp B S hS 𝓖 g.unop g'.unop

/-! ### Semilinearity of the restriction maps -/

section Smul

variable {B}

/-- **Sections over an object of a morphism of sheaves of modules are linear**: the morphism's
component at the object is a morphism of modules, and `smallEtaleSectionsApp` is its underlying
additive map. -/
public theorem smallEtaleSectionsApp_smul {X : B.Scheme}
    {M N : SheafOfModules.{u} (structureSheaf B X.obj X.property)} (φ : M ⟶ N)
    (W : SmallEtale B X.obj X.property)
    (r : (structureSheaf B X.obj X.property).obj.obj (op W)) (x : M.val.obj (op W)) :
    (smallEtaleSectionsApp B φ W).hom (r • x) = r • (smallEtaleSectionsApp B φ W).hom x :=
  map_smul (φ.val.app (op W)).hom r x

/-- The structure map of `ε_a` of Stacks 070R (2) on sections over an object, with its target
spelled as the sections of the structure sheaf of the small étale site of `X` over the base
change of that object; this is the spelling at which the module structures are found. -/
public abbrev structureMapAppSections {X Y : B.Scheme} (a : X ⟶ Y)
    (U : SmallEtale B Y.obj Y.property)
    (r : (structureSheaf B Y.obj Y.property).obj.obj (op U)) :
    (structureSheaf B X.obj X.property).obj.obj (op ((smallEtaleBaseChange B a).obj U)) :=
  ((smallEtaleStructureMapRing B a).hom.app (op U)).hom r

/-- **The unit along `ε_a`, read on sections, is semilinear along the structure map of `ε_a`.**
The target is the sections of a direct image, whose scalars are restricted along that structure
map, so this is `AlgebraicGeometry.SmallEtale.smallEtaleSectionsApp_smul` with the restriction
of scalars spelled out. -/
public theorem unitSectionsApp_smul {X Y : B.Scheme} (a : X ⟶ Y)
    (M : SheafOfModules.{u} (structureSheaf B Y.obj Y.property))
    (U : SmallEtale B Y.obj Y.property)
    (r : (structureSheaf B Y.obj Y.property).obj.obj (op U))
    (x : M.val.obj (op U)) :
    (unitSectionsApp B a M U).hom (r • x) =
      structureMapAppSections a U r • (unitSectionsApp B a M U).hom x :=
  smallEtaleSectionsApp_smul _ U r x

/-- **`finalPullbackUnit` is semilinear**, along the structure map of `ε_a` at the final object
followed by restriction along the canonical arrow of
`AlgebraicGeometry.SmallEtale.smallEtaleBaseChange_finalIsTerminal`. -/
public theorem finalPullbackUnit_smul {X Y : B.Scheme} (a : X ⟶ Y)
    (M : SheafOfModules.{u} (structureSheaf B Y.obj Y.property))
    (r : (structureSheaf B Y.obj Y.property).obj.obj (op (final B Y.obj Y.property)))
    (x : M.val.obj (op (final B Y.obj Y.property))) :
    (finalPullbackUnit B a M).hom (r • x) =
      ((structureSheaf B X.obj X.property).obj.map
            ((smallEtaleBaseChange_finalIsTerminal B a).from
              (final B X.obj X.property)).op).hom
          (structureMapAppSections a (final B Y.obj Y.property) r) •
        (finalPullbackUnit B a M).hom x := by
  show ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).obj
      M).val.presheaf.map _ ((unitSectionsApp B a M _).hom (r • x)) = _
  rw [unitSectionsApp_smul]
  exact PresheafOfModules.map_smul _ _ _ _

/-- **The canonical arrow into the base change of the final object is a section of the second
projection and lands on `a` under the first.**  Over `X` the base change of `S / S` along
`a : X ⟶ Y` is `X ×_Y Y`, whose structure morphism is the second projection; the canonical
arrow from `X / X` is therefore a section of it, and composing with the first projection gives
`a` because the first projection factors through the second. -/
public theorem terminalFrom_final_left_comp_pullback_fst {X Y : B.Scheme} (a : X ⟶ Y) :
    ((inclusion B X.obj X.property).map
          ((smallEtaleBaseChange_finalIsTerminal B a).from (final B X.obj X.property))).left ≫
        Limits.pullback.fst (final B Y.obj Y.property).obj.hom a =
      a := by
  have hw : ((inclusion B X.obj X.property).map
        ((smallEtaleBaseChange_finalIsTerminal B a).from
          (final B X.obj X.property))).left ≫
      Limits.pullback.snd (final B Y.obj Y.property).obj.hom a = 𝟙 _ := Over.w _
  have hcond : Limits.pullback.fst (final B Y.obj Y.property).obj.hom a =
      Limits.pullback.snd (final B Y.obj Y.property).obj.hom a ≫ a := by
    rw [← Limits.pullback.condition]
    exact (Category.comp_id _).symm
  exact (congrArg (fun t => ((inclusion B X.obj X.property).map
        ((smallEtaleBaseChange_finalIsTerminal B a).from
          (final B X.obj X.property))).left ≫ t) hcond).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ a) hw).trans (Category.id_comp a)))

/-- **The semilinearity scalar of `AlgebraicGeometry.SmallEtale.finalPullbackUnit` is pullback
of global functions along `a`.**  Both factors are pullback of functions — along the projection
`X ×_Y Y ⟶ Y` and along the canonical arrow `X ⟶ X ×_Y Y` — and their composite is pullback
along `a`, by
`AlgebraicGeometry.SmallEtale.terminalFrom_final_left_comp_pullback_fst`. -/
public theorem structureSheaf_map_structureMapAppSections {X Y : B.Scheme} (a : X ⟶ Y)
    (r : (structureSheaf B Y.obj Y.property).obj.obj (op (final B Y.obj Y.property))) :
    ((structureSheaf B X.obj X.property).obj.map
          ((smallEtaleBaseChange_finalIsTerminal B a).from
            (final B X.obj X.property)).op).hom
        (structureMapAppSections a (final B Y.obj Y.property) r) =
      ((forget₂ CommRingCat.{u} RingCat.{u}).map
        (Scheme.Γ.map (op (B.inclusion.map a)))).hom r := by
  have h := congrArg (fun k => (forget₂ CommRingCat.{u} RingCat.{u}).map
      (Scheme.Γ.map (op (B.inclusion.map k))))
    (terminalFrom_final_left_comp_pullback_fst a)
  simp only at h
  exact congrFun (congrArg (fun t : (_ : RingCat.{u}) ⟶ _ => t.hom.toFun) h) r

end Smul

/-! ### The presheaf of modules -/

/-- The structure presheaf of rings of the big étale category over `S`: global functions on the
underlying scheme. -/
public abbrev bigEtaleOverRing : (BigEtaleOver B S hS)ᵒᵖ ⥤ RingCat.{u} :=
  (BigEtaleOver.toScheme B S hS).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat.{u} RingCat.{u}

/-- The restriction map of `AlgebraicGeometry.SmallEtale.bigEtaleOverRing` along `g`, with its
target spelled as the sections of the small étale structure sheaf over the final object; this is
the spelling at which the module structure of the sections rule is found. -/
public abbrev sectionsSheafTauRingMap {T T' : BigEtaleOver B S hS} (g : T' ⟶ T)
    (r : (structureSheaf B T.left.obj T.left.property).obj.obj
      (op (final B T.left.obj T.left.property))) :
    (structureSheaf B T'.left.obj T'.left.property).obj.obj
      (op (final B T'.left.obj T'.left.property)) :=
  ((forget₂ CommRingCat.{u} RingCat.{u}).map
    (Scheme.Γ.map (op (B.inclusion.map g.left)))).hom r

/-- **The restriction maps of the sections rule are semilinear.**  The two factors are
`AlgebraicGeometry.SmallEtale.finalPullbackUnit_smul`, whose scalar is identified with pullback
of functions along `g` by
`AlgebraicGeometry.SmallEtale.structureSheaf_map_structureMapAppSections`, and
`AlgebraicGeometry.SmallEtale.smallEtaleSectionsApp_smul`, which is linear. -/
public theorem sectionsSheafTauMap_smul {T T' : BigEtaleOver B S hS} (g : T' ⟶ T)
    (r : (structureSheaf B T.left.obj T.left.property).obj.obj
      (op (final B T.left.obj T.left.property)))
    (m : (sectionsSheafTauPullback B S hS 𝓖 T).val.obj
      (op (final B T.left.obj T.left.property))) :
    (sectionsSheafTauMap B S hS 𝓖 g).hom (r • m) =
      sectionsSheafTauRingMap B S hS g r • (sectionsSheafTauMap B S hS 𝓖 g).hom m := by
  refine Eq.trans ?_ (congrArg (fun s => s • (sectionsSheafTauMap B S hS 𝓖 g).hom m)
    (structureSheaf_map_structureMapAppSections g.left r))
  show (smallEtaleSectionsApp B
      ((smallEtalePullbackFactoredCompIso B g.left T.hom T'.hom (Over.w g)).hom.app 𝓖)
      (final B T'.left.obj T'.left.property)).hom
      ((finalPullbackUnit B g.left (sectionsSheafTauPullback B S hS 𝓖 T)).hom (r • m)) = _
  rw [finalPullbackUnit_smul]
  exact smallEtaleSectionsApp_smul _ _ _ _

/-- The value of `AlgebraicGeometry.SmallEtale.sectionsSheafTauPresheaf` at `T` is a module over
the ring of global sections of `T`. -/
public instance moduleSectionsSheafTauObj (T : (BigEtaleOver B S hS)ᵒᵖ) :
    Module ((bigEtaleOverRing B S hS).obj T) ((sectionsSheafTauPresheaf B S hS 𝓖).obj T) :=
  inferInstanceAs (Module ((structureSheaf B T.unop.left.obj T.unop.left.property).obj.obj
      (op (final B T.unop.left.obj T.unop.left.property)))
    ((sectionsSheafTauPullback B S hS 𝓖 T.unop).val.obj
      (op (final B T.unop.left.obj T.unop.left.property))))

/-- **The sections rule `(f : T → S) ↦ Γ(T, f_small^*𝓖)` as a presheaf of `𝒪`-modules** on the
big étale category over `S`. This is the presheaf whose `τ`-sheafification **Stacks 070S
part (3)** identifies with `(id_{τ,étale})^*𝓖`, for an arbitrary sheaf of `𝒪`-modules `𝓖` on
`S_étale`. -/
public def sectionsSheafTauPresheafOfModules :
    PresheafOfModules.{u} (bigEtaleOverRing B S hS) :=
  PresheafOfModules.ofPresheaf (sectionsSheafTauPresheaf B S hS 𝓖)
    (fun {_ _} f r m => sectionsSheafTauMap_smul B S hS 𝓖 f.unop r m)

/-- The presheaf of abelian groups underlying
`AlgebraicGeometry.SmallEtale.sectionsSheafTauPresheafOfModules` is the sections rule. -/
@[simp]
public theorem sectionsSheafTauPresheafOfModules_presheaf :
    (sectionsSheafTauPresheafOfModules B S hS 𝓖).presheaf =
      sectionsSheafTauPresheaf B S hS 𝓖 :=
  rfl

/-! ### The diagonal arrow -/

section Diagonal

variable {B}

/-- **The diagonal arrow.**  For an object `V` of the small étale site of `Y`, with structure
morphism `v : V → Y`, the base change of `V` along `v` is `V ×_Y V`, whose structure morphism to
`V` is the second projection; the diagonal is the resulting arrow from the final object `V / V`
of the small étale site of `V`. -/
public def finalToSelfBaseChange {Z : Scheme.{u}} {hZ : B.Contains Z}
    (V : SmallEtale B Z hZ) :
    final B V.obj.left.obj V.obj.left.property ⟶
      (smallEtaleBaseChange B V.obj.hom).obj V :=
  ObjectProperty.homMk (Over.homMk
    (Limits.pullback.lift (𝟙 _) (𝟙 _) rfl) (Limits.pullback.lift_snd _ _ _))

/-- The diagonal arrow is a section of the first projection as well. -/
public theorem finalToSelfBaseChange_left_comp_fst {Z : Scheme.{u}} {hZ : B.Contains Z}
    (V : SmallEtale B Z hZ) :
    (finalToSelfBaseChange V).hom.left ≫
        Limits.pullback.fst V.obj.hom V.obj.hom =
      𝟙 _ :=
  Limits.pullback.lift_fst _ _ _

/-- `AlgebraicGeometry.SmallEtale.finalToSelfBaseChange_left_comp_fst` with a trailing factor,
which is the right-associated shape the identities below have. -/
public theorem finalToSelfBaseChange_left_comp_fst_comp {Z : Scheme.{u}} {hZ : B.Contains Z}
    (V : SmallEtale B Z hZ) {R : B.Scheme} (m : V.obj.left ⟶ R) :
    (finalToSelfBaseChange V).hom.left ≫
        Limits.pullback.fst V.obj.hom V.obj.hom ≫ m =
      m :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ m) (finalToSelfBaseChange_left_comp_fst V)).trans (Category.id_comp m))

/-- `AlgebraicGeometry.SmallEtale.terminalFrom_final_left_comp_pullback_fst` in the `hom.left`
spelling the projection lemmas of Stacks 021J use. -/
public theorem terminalFrom_final_hom_left_comp_fst {X Y : B.Scheme} (a : X ⟶ Y) :
    ((smallEtaleBaseChange_finalIsTerminal B a).from (final B X.obj X.property)).hom.left ≫
        Limits.pullback.fst (final B Y.obj Y.property).obj.hom a =
      a :=
  terminalFrom_final_left_comp_pullback_fst a

/-- The canonical arrow into the base change of the final object, followed by base change of the
diagonal of `V` and the comparison of **Stacks 021J**, projects to `a` under the first
projection. -/
private theorem terminalFrom_comp_map_finalToSelfBaseChange_comp_fst {Z : Scheme.{u}}
    {hZ : B.Contains Z} (V : SmallEtale B Z hZ) {W : B.Scheme} (a : W ⟶ V.obj.left)
    (c : W ⟶ B.obj Z hZ) (h : a ≫ V.obj.hom = c) :
    ((smallEtaleBaseChange_finalIsTerminal B a).from (final B W.obj W.property)).hom.left ≫
        ((smallEtaleBaseChange B a).map (finalToSelfBaseChange V)).hom.left ≫
          ((smallEtaleBaseChange_factoredCompIso B W V.obj.left (B.obj Z hZ) a V.obj.hom c
            h).hom.app V).hom.left ≫ Limits.pullback.fst V.obj.hom c = a := by
  rw [smallEtaleBaseChange_factoredCompIso_hom_app_fst]
  refine (congrArg (_ ≫ ·) (smallEtaleBaseChange_map_hom_left_comp_fst_comp B a
    (finalToSelfBaseChange V) (Limits.pullback.fst V.obj.hom V.obj.hom))).trans ?_
  rw [finalToSelfBaseChange_left_comp_fst]
  exact (congrArg (_ ≫ ·) (Category.comp_id _)).trans (terminalFrom_final_hom_left_comp_fst a)

/-- **The diagonal is natural in the object**, in the form the sections rule consumes: for
`k : V' ⟶ V` in the small étale site of `Y`, with `κ` the underlying morphism of schemes and
`κ ≫ v = v'` the resulting factorization, the diagonal of `V'` followed by base change of `k`
agrees with the canonical arrow into the base change of the final object, followed by base
change of the diagonal of `V`, followed by the comparison of **Stacks 021J**.

Both sides are morphisms into a base change along `v'`, so by
`AlgebraicGeometry.SmallEtale.hom_ext_of_comp_fst_smallEtaleBaseChange` it suffices to compose
with the projection upstairs, and the two projection identities of Stacks 021J together with
`AlgebraicGeometry.SmallEtale.finalToSelfBaseChange_left_comp_fst` and
`AlgebraicGeometry.SmallEtale.terminalFrom_final_hom_left_comp_fst` carry both to `κ`. -/
public theorem finalToSelfBaseChange_naturality {Z : Scheme.{u}} {hZ : B.Contains Z}
    {V V' : SmallEtale B Z hZ} (k : V' ⟶ V) :
    finalToSelfBaseChange V' ≫ (smallEtaleBaseChange B V'.obj.hom).map k =
      (smallEtaleBaseChange_finalIsTerminal B k.hom.left).from
            (final B V'.obj.left.obj V'.obj.left.property) ≫
          (smallEtaleBaseChange B k.hom.left).map (finalToSelfBaseChange V) ≫
        (smallEtaleBaseChange_factoredCompIso B V'.obj.left V.obj.left
          (B.obj Z hZ) k.hom.left V.obj.hom V'.obj.hom (Over.w k.hom)).hom.app V := by
  refine hom_ext_of_comp_fst_smallEtaleBaseChange B V'.obj.hom _ _ ?_
  have hL : (finalToSelfBaseChange V').hom.left ≫
        ((smallEtaleBaseChange B V'.obj.hom).map k).hom.left ≫
          Limits.pullback.fst V.obj.hom V'.obj.hom =
      k.hom.left :=
    (congrArg (fun t => (finalToSelfBaseChange V').hom.left ≫ t)
        (smallEtaleBaseChange_map_hom_left_comp_fst B V'.obj.hom k)).trans
      (finalToSelfBaseChange_left_comp_fst_comp V' k.hom.left)
  have hR := terminalFrom_comp_map_finalToSelfBaseChange_comp_fst V k.hom.left V'.obj.hom
    (Over.w k.hom)
  simp only [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left]
  exact ((Category.assoc _ _ _).trans hL).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun t => ((smallEtaleBaseChange_finalIsTerminal B k.hom.left).from
            (final B V'.obj.left.obj V'.obj.left.property)).hom.left ≫ t)
          (Category.assoc _ _ _)).trans hR)).symm

end Diagonal

/-! ### The unit law of Stacks 070R (2) on sections over an arbitrary object -/

section UnitObj

variable {B}

/-- **The unit law for the composition of the pullbacks of Stacks 070R (2), read on sections
over an arbitrary object.**  This is
`AlgebraicGeometry.SmallEtale.smallEtalePullbackUnit_factoredComp` with every factor evaluated
on sections over `U`; the `final`-only instance is
`AlgebraicGeometry.SmallEtale.unitSectionsApp_factoredComp`. -/
public theorem unitSectionsApp_factoredComp_obj {W X Y : B.Scheme}
    (a₂ : W ⟶ X) (a₁ : X ⟶ Y) (a : W ⟶ Y) (ha : a₂ ≫ a₁ = a)
    (M : SheafOfModules.{u} (structureSheaf B Y.obj Y.property))
    (U : SmallEtale B Y.obj Y.property) :
    unitSectionsApp B a₁ M U ≫
        unitSectionsApp B a₂
            ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a₁)).obj M)
            ((smallEtaleBaseChange B a₁).obj U) ≫
          ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a₂)).obj
              ((SheafOfModules.pullback.{u}
                (smallEtaleStructureMapRing B a₁)).obj M)).val.presheaf.map
              ((smallEtaleBaseChange_factoredCompIso B W X Y a₂ a₁ a ha).inv.app U).op ≫
            smallEtaleSectionsApp B
              ((smallEtalePullbackFactoredCompIso B a₂ a₁ a ha).hom.app M)
              ((smallEtaleBaseChange B a).obj U) =
      unitSectionsApp B a M U := by
  have hU := congrArg (fun t => smallEtaleSectionsApp B t U)
    (smallEtalePullbackUnit_factoredComp B a₂ a₁ a ha M)
  simp only [smallEtaleSectionsApp_comp] at hU
  rw [pushforward_map_sectionsApp, pushforwardRightCompIso_sectionsApp,
    pushforward_map_sectionsApp] at hU
  exact hU

/-- `AlgebraicGeometry.SmallEtale.unitSectionsApp_factoredComp_obj` with a restriction along an
arrow `c` into the base change along the composite appended on both sides: the restriction map
commutes with the comparison by
`AlgebraicGeometry.SmallEtale.smallEtaleSectionsApp_naturality`, and what is left is the unit law
itself. -/
public theorem unitSectionsApp_factoredComp_obj_comp {W X Y : B.Scheme}
    (a₂ : W ⟶ X) (a₁ : X ⟶ Y) (a : W ⟶ Y) (ha : a₂ ≫ a₁ = a)
    (M : SheafOfModules.{u} (structureSheaf B Y.obj Y.property))
    (U : SmallEtale B Y.obj Y.property) (U' : SmallEtale B W.obj W.property)
    (c : U' ⟶ (smallEtaleBaseChange B a).obj U) :
    unitSectionsApp B a₁ M U ≫
        unitSectionsApp B a₂
            ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a₁)).obj M)
            ((smallEtaleBaseChange B a₁).obj U) ≫
          ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a₂)).obj
              ((SheafOfModules.pullback.{u}
                (smallEtaleStructureMapRing B a₁)).obj M)).val.presheaf.map
              (c ≫ (smallEtaleBaseChange_factoredCompIso B W X Y a₂ a₁ a ha).inv.app U).op ≫
            smallEtaleSectionsApp B
              ((smallEtalePullbackFactoredCompIso B a₂ a₁ a ha).hom.app M) U' =
      unitSectionsApp B a M U ≫
        ((SheafOfModules.pullback.{u}
          (smallEtaleStructureMapRing B a)).obj M).val.presheaf.map c.op := by
  have hnat := smallEtaleSectionsApp_naturality B
    ((smallEtalePullbackFactoredCompIso B a₂ a₁ a ha).hom.app M) c
  simp only [Functor.comp_obj] at hnat
  have hbase := unitSectionsApp_factoredComp_obj a₂ a₁ a ha M U
  rw [op_comp, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  slice_lhs 4 5 => rw [hnat]
  slice_lhs 1 4 => rw [hbase]

end UnitObj

/-! ### The localization map `𝓖 ⟶ (sections rule)|_{S_étale}` -/

/-- **The localization map on sections over an étale `V / S`**: the unit along `ε_v` read on
sections over `V`, followed by restriction along the diagonal.  Its target is the value of the
sections rule at the object `V / S` of the big site. -/
public def sectionsSheafTauLocApp (V : SmallEtale B S hS) :
    𝓖.val.presheaf.obj (op V) ⟶
      ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B V.obj.hom)).obj
        𝓖).val.presheaf.obj (op (final B V.obj.left.obj V.obj.left.property)) :=
  unitSectionsApp B V.obj.hom 𝓖 V ≫
    ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B V.obj.hom)).obj
      𝓖).val.presheaf.map (finalToSelfBaseChange V).op

/-- **The localization map is natural in `V`.**  The two units involved are for different
morphisms — `v'` on the left and `v` on the right — so what brings them into contact is the
unit law of Stacks 070R (2) over an arbitrary object,
`AlgebraicGeometry.SmallEtale.unitSectionsApp_factoredComp_obj`; the remaining geometry is
`AlgebraicGeometry.SmallEtale.finalToSelfBaseChange_naturality`. -/
public theorem sectionsSheafTauLocApp_naturality {V V' : SmallEtale B S hS} (k : V' ⟶ V) :
    𝓖.val.presheaf.map k.op ≫ sectionsSheafTauLocApp B S hS 𝓖 V' =
      sectionsSheafTauLocApp B S hS 𝓖 V ≫
        sectionsSheafTauMap B S hS 𝓖 k.hom := by
  have hv : k.hom.left ≫ V.obj.hom = V'.obj.hom := Over.w k.hom
  have hfu := congrArg (fun t => smallEtaleSectionsApp B t V)
    (smallEtalePullbackUnit_factoredComp B k.hom.left V.obj.hom V'.obj.hom hv 𝓖)
  simp only [smallEtaleSectionsApp_comp (X := B.obj S hS)] at hfu
  rw [pushforward_map_sectionsApp, pushforwardRightCompIso_sectionsApp,
    pushforward_map_sectionsApp] at hfu
  have hnat := finalToSelfBaseChange_naturality k
  simp only [sectionsSheafTauLocApp, sectionsSheafTauMap, finalPullbackUnit, Category.assoc]
  slice_lhs 1 2 => rw [unitSectionsApp_naturality_obj B V'.obj.hom 𝓖 k]
  slice_lhs 2 3 => rw [← CategoryTheory.Functor.map_comp, ← op_comp, hnat]
  slice_rhs 2 3 => rw [unitSectionsApp_naturality_obj]
  simp only [unitSectionsApp]
  rw [← hfu]
  simp only [Category.assoc]
  have hkey : (((smallEtaleBaseChange_finalIsTerminal B k.hom.left).from
      (final B V'.obj.left.obj V'.obj.left.property)) ≫ ((smallEtaleBaseChange B k.hom.left).map
        (finalToSelfBaseChange V)) ≫ (smallEtaleBaseChange_factoredCompIso B V'.obj.left V.obj.left
        (B.obj S hS)
      k.hom.left V.obj.hom V'.obj.hom hv).hom.app V) ≫
        (smallEtaleBaseChange_factoredCompIso B V'.obj.left V.obj.left (B.obj S hS)
      k.hom.left V.obj.hom V'.obj.hom hv).inv.app V =
      ((smallEtaleBaseChange_finalIsTerminal B k.hom.left).from
      (final B V'.obj.left.obj V'.obj.left.property)) ≫ ((smallEtaleBaseChange B k.hom.left).map
        (finalToSelfBaseChange V)) := by
    simp
  have hDE : smallEtaleSectionsApp B
      ((smallEtalePullbackFactoredCompIso B k.hom.left V.obj.hom V'.obj.hom hv).hom.app 𝓖)
          ((smallEtaleBaseChange B V'.obj.hom).obj V) ≫
        ((SheafOfModules.pullback.{u}
          (smallEtaleStructureMapRing B V'.obj.hom)).obj 𝓖).val.presheaf.map
          (((smallEtaleBaseChange_finalIsTerminal B k.hom.left).from
      (final B V'.obj.left.obj V'.obj.left.property)) ≫ ((smallEtaleBaseChange B k.hom.left).map
        (finalToSelfBaseChange V)) ≫ (smallEtaleBaseChange_factoredCompIso B V'.obj.left V.obj.left
        (B.obj S hS)
      k.hom.left V.obj.hom V'.obj.hom hv).hom.app V).op =
      ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B k.hom.left)).obj
      ((SheafOfModules.pullback.{u}
        (smallEtaleStructureMapRing B V.obj.hom)).obj 𝓖)).val.presheaf.map
          (((smallEtaleBaseChange_finalIsTerminal B k.hom.left).from
      (final B V'.obj.left.obj V'.obj.left.property)) ≫ ((smallEtaleBaseChange B k.hom.left).map
        (finalToSelfBaseChange V)) ≫ (smallEtaleBaseChange_factoredCompIso B V'.obj.left V.obj.left
        (B.obj S hS)
      k.hom.left V.obj.hom V'.obj.hom hv).hom.app V).op ≫
        smallEtaleSectionsApp B
          ((smallEtalePullbackFactoredCompIso B k.hom.left V.obj.hom V'.obj.hom hv).hom.app 𝓖)
          (final B V'.obj.left.obj V'.obj.left.property) :=
    (smallEtaleSectionsApp_naturality B _ _).symm
  have hCE : ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B k.hom.left)).obj
      ((SheafOfModules.pullback.{u}
        (smallEtaleStructureMapRing B V.obj.hom)).obj 𝓖)).val.presheaf.map
        ((smallEtaleBaseChange_factoredCompIso B V'.obj.left V.obj.left (B.obj S hS)
      k.hom.left V.obj.hom V'.obj.hom hv).inv.app V).op ≫
        ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B k.hom.left)).obj
      ((SheafOfModules.pullback.{u}
        (smallEtaleStructureMapRing B V.obj.hom)).obj 𝓖)).val.presheaf.map
          (((smallEtaleBaseChange_finalIsTerminal B k.hom.left).from
      (final B V'.obj.left.obj V'.obj.left.property)) ≫ ((smallEtaleBaseChange B k.hom.left).map
        (finalToSelfBaseChange V)) ≫ (smallEtaleBaseChange_factoredCompIso B V'.obj.left V.obj.left
        (B.obj S hS)
      k.hom.left V.obj.hom V'.obj.hom hv).hom.app V).op =
      ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B k.hom.left)).obj
      ((SheafOfModules.pullback.{u}
        (smallEtaleStructureMapRing B V.obj.hom)).obj 𝓖)).val.presheaf.map
        ((smallEtaleBaseChange B k.hom.left).map (finalToSelfBaseChange V)).op ≫
        ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B k.hom.left)).obj
      ((SheafOfModules.pullback.{u}
        (smallEtaleStructureMapRing B V.obj.hom)).obj 𝓖)).val.presheaf.map
        ((smallEtaleBaseChange_finalIsTerminal B k.hom.left).from
      (final B V'.obj.left.obj V'.obj.left.property)).op := by
    rw [← CategoryTheory.Functor.map_comp, ← op_comp, hkey, op_comp,
      CategoryTheory.Functor.map_comp]
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine congrArg (fun t => _ ≫ t) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg (fun t => _ ≫ t) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun t => _ ≫ t) hDE) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact (congrArg (fun t => t ≫ _) hCE).trans (Category.assoc _ _ _)


/-- A section of the structure sheaf over an étale `V / S`, read as a section over the final
object of the small étale site of the scheme of `V`; the two are the same ring, namely the
global functions of that scheme, and this pins the spelling at which the module structures of
the sections rule are found. -/
public abbrev locScalar (V : SmallEtale B S hS)
    (r : (structureSheaf B S hS).obj.obj (op V)) :
    (structureSheaf B V.obj.left.obj V.obj.left.property).obj.obj
      (op (final B V.obj.left.obj V.obj.left.property)) :=
  r

/-- **The semilinearity scalar of the localization map is the identity.**  The two factors are
pullback of functions along the projection `V ×_S V ⟶ V` and along the diagonal, whose
composite is the identity by
`AlgebraicGeometry.SmallEtale.finalToSelfBaseChange_left_comp_fst`. -/
public theorem structureSheaf_map_diag_structureMapAppSections (V : SmallEtale B S hS)
    (r : (structureSheaf B S hS).obj.obj (op V)) :
    ((structureSheaf B V.obj.left.obj V.obj.left.property).obj.map
          (finalToSelfBaseChange V).op).hom
        (structureMapAppSections V.obj.hom V r) =
      locScalar B S hS V r := by
  have h := congrArg (fun k => (forget₂ CommRingCat.{u} RingCat.{u}).map
      (Scheme.Γ.map (op (B.inclusion.map k))))
    (finalToSelfBaseChange_left_comp_fst V)
  simp only at h
  exact congrFun (congrArg (fun t : (_ : RingCat.{u}) ⟶ _ => t.hom.toFun) h) r

/-- **The localization map is linear.**  Its first factor is semilinear along the structure map
of `ε_v` and its second along restriction to the diagonal, and that composite of ring maps is
the identity. -/
public theorem sectionsSheafTauLocApp_smul (V : SmallEtale B S hS)
    (r : (structureSheaf B S hS).obj.obj (op V)) (x : 𝓖.val.obj (op V)) :
    (sectionsSheafTauLocApp B S hS 𝓖 V).hom (r • x) =
      locScalar B S hS V r • (sectionsSheafTauLocApp B S hS 𝓖 V).hom x := by
  refine Eq.trans ?_ (congrArg (fun s => s • (sectionsSheafTauLocApp B S hS 𝓖 V).hom x)
    (structureSheaf_map_diag_structureMapAppSections B S hS V r))
  show ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B V.obj.hom)).obj
      𝓖).val.presheaf.map _ ((unitSectionsApp B V.obj.hom 𝓖 V).hom (r • x)) = _
  rw [unitSectionsApp_smul]
  exact PresheafOfModules.map_smul _ _ _ _


/-! ### The sections rule read on the small étale site of an object -/

section Restricted

variable (T : BigEtaleOver B S hS)

/-- **The sections rule at `W / S`, compared with the sections of `f_small^*𝓖` at `W`**, for an
object `W` of the small étale site of the scheme of `T / S` and a chosen factorization
`w ≫ f = g`.  This is the localization map of the small étale site of the scheme of `T`, applied
to the sheaf `f_small^*𝓖`, followed by the composition law of Stacks 070R (2) at that
factorization.

The factorization is chosen rather than taken to be `w ≫ f` because `𝟙 ≫ f = f` is not an
equality of terms in the size-bounded category of a big étale site; choosing it is what lets
the instance at the final object be stated about `T` itself. -/
public def sectionsSheafTauRho (W : SmallEtale B T.left.obj T.left.property)
    (g : W.obj.left ⟶ B.obj S hS) (hg : W.obj.hom ≫ T.hom = g) :
    (sectionsSheafTauPullback B S hS 𝓖 T).val.presheaf.obj (op W) ⟶
      sectionsSheafTauObj B S hS 𝓖 (Over.mk g) :=
  sectionsSheafTauLocApp B T.left.obj T.left.property
      (sectionsSheafTauPullback B S hS 𝓖 T) W ≫
    smallEtaleSectionsApp B
      ((smallEtalePullbackFactoredCompIso B W.obj.hom T.hom g hg).hom.app 𝓖)
      (final B W.obj.left.obj W.obj.left.property)

/-- **`finalPullbackUnit` along the structure morphism of `W` is restriction to `W` followed by
the localization map.**  Both sides start with the unit along `ε_w` over the final object, and
what remains is that the diagonal of `W` followed by base change of the canonical arrow
`W ⟶ T / T` agrees with the canonical arrow into the base change of the final object — which it
does, that base change being terminal. -/
public theorem finalPullbackUnit_eq_locApp (W : SmallEtale B T.left.obj T.left.property) :
    finalPullbackUnit B W.obj.hom (sectionsSheafTauPullback B S hS 𝓖 T) =
      (sectionsSheafTauPullback B S hS 𝓖 T).val.presheaf.map
          ((finalIsTerminal B T.left.obj T.left.property).from W).op ≫
        sectionsSheafTauLocApp B T.left.obj T.left.property
          (sectionsSheafTauPullback B S hS 𝓖 T) W := by
  have hterm : finalToSelfBaseChange W ≫
        (smallEtaleBaseChange B W.obj.hom).map
          ((finalIsTerminal B T.left.obj T.left.property).from W) =
      (smallEtaleBaseChange_finalIsTerminal B W.obj.hom).from
        (final B W.obj.left.obj W.obj.left.property) :=
    (smallEtaleBaseChange_finalIsTerminal B W.obj.hom).hom_ext _ _
  have hnat := unitSectionsApp_naturality_obj B W.obj.hom
    (sectionsSheafTauPullback B S hS 𝓖 T)
    ((finalIsTerminal B T.left.obj T.left.property).from W)
  simp only [finalPullbackUnit, sectionsSheafTauLocApp]
  slice_rhs 1 2 => rw [hnat]
  slice_rhs 2 3 => rw [← CategoryTheory.Functor.map_comp, ← op_comp, hterm]

/-- **The restriction maps of the sections rule along an étale `W → T` are the restriction maps
of `f_small^*𝓖` itself**, followed by the comparison
`AlgebraicGeometry.SmallEtale.sectionsSheafTauRho`.  This is the identity that makes the local
surjectivity and local injectivity of the comparison of **Stacks 070S part (3)** reduce to local
bijectivity of the sheafification unit on the small étale site of `T`. -/
public theorem sectionsSheafTauMap_eq_rho (W : SmallEtale B T.left.obj T.left.property)
    (g : W.obj.left ⟶ B.obj S hS) (hg : W.obj.hom ≫ T.hom = g) :
    sectionsSheafTauMap B S hS 𝓖 (Over.homMk W.obj.hom hg : Over.mk g ⟶ T) =
      (sectionsSheafTauPullback B S hS 𝓖 T).val.presheaf.map
          ((finalIsTerminal B T.left.obj T.left.property).from W).op ≫
        sectionsSheafTauRho B S hS 𝓖 T W g hg :=
  (congrArg (fun t => t ≫ smallEtaleSectionsApp B
      ((smallEtalePullbackFactoredCompIso B W.obj.hom T.hom g hg).hom.app 𝓖)
      (final B W.obj.left.obj W.obj.left.property))
    (finalPullbackUnit_eq_locApp B S hS 𝓖 T W)).trans (Category.assoc _ _ _)


/-- **At the final object, with the factorization `f` itself, `ρ'` is the identity.**  The
object `Over.mk f` is `T` and the canonical arrow `W ⟶ T / T` is the identity, so
`AlgebraicGeometry.SmallEtale.sectionsSheafTauMap_eq_rho` reads `ρ'` as the restriction map of
the sections rule along the identity of `T`, which is the identity by
`AlgebraicGeometry.SmallEtale.sectionsSheafTauMap_id`.

This is why the factorization is an argument of `sectionsSheafTauRho` rather than being taken to
be `w ≫ f`: at `W = T / T` the chosen factorization can be `f` on the nose, and then the target
of `ρ'` is the sections rule at `T` itself. -/
public theorem sectionsSheafTauRho_final
    (hg : (final B T.left.obj T.left.property).obj.hom ≫ T.hom = T.hom) :
    sectionsSheafTauRho B S hS 𝓖 T (final B T.left.obj T.left.property) T.hom hg = 𝟙 _ := by
  have hid : (Over.homMk (final B T.left.obj T.left.property).obj.hom hg :
      Over.mk T.hom ⟶ T) = 𝟙 T := by
    apply Over.OverMorphism.ext
    rfl
  have hterm : (finalIsTerminal B T.left.obj T.left.property).from
      (final B T.left.obj T.left.property) = 𝟙 _ :=
    (finalIsTerminal B T.left.obj T.left.property).hom_ext _ _
  have key := sectionsSheafTauMap_eq_rho B S hS 𝓖 T (final B T.left.obj T.left.property)
    T.hom hg
  have h1 : (𝟙 (sectionsSheafTauObj B S hS 𝓖 T) :
        sectionsSheafTauObj B S hS 𝓖 T ⟶ sectionsSheafTauObj B S hS 𝓖 T) =
      (sectionsSheafTauPullback B S hS 𝓖 T).val.presheaf.map
          ((finalIsTerminal B T.left.obj T.left.property).from
            (final B T.left.obj T.left.property)).op ≫
        sectionsSheafTauRho B S hS 𝓖 T (final B T.left.obj T.left.property) T.hom hg :=
    (sectionsSheafTauMap_id B S hS 𝓖 T).symm.trans
      ((congrArg (fun g : Over.mk T.hom ⟶ T => sectionsSheafTauMap B S hS 𝓖 g) hid).symm.trans
        key)
  have h2 : (sectionsSheafTauPullback B S hS 𝓖 T).val.presheaf.map
        ((finalIsTerminal B T.left.obj T.left.property).from
          (final B T.left.obj T.left.property)).op =
      𝟙 (sectionsSheafTauObj B S hS 𝓖 T) :=
    (congrArg (fun k : final B T.left.obj T.left.property ⟶
          final B T.left.obj T.left.property =>
        (sectionsSheafTauPullback B S hS 𝓖 T).val.presheaf.map k.op) hterm).trans
      ((sectionsSheafTauPullback B S hS 𝓖 T).val.presheaf.map_id
        (op (final B T.left.obj T.left.property)))
  exact (h1.trans ((congrArg (fun t : sectionsSheafTauObj B S hS 𝓖 T ⟶
          sectionsSheafTauObj B S hS 𝓖 T =>
        t ≫ sectionsSheafTauRho B S hS 𝓖 T (final B T.left.obj T.left.property) T.hom hg)
      h2).trans (Category.id_comp _))).symm

/-- **The comparison `AlgebraicGeometry.SmallEtale.sectionsSheafTauRho` is natural in `W`.**
Structurally this is the same identity as
`AlgebraicGeometry.SmallEtale.sectionsSheafTauMap_comp`: after cancelling the localization map
and the pullback unit — the first by
`AlgebraicGeometry.SmallEtale.sectionsSheafTauLocApp_naturality` for the base `T`, the second by
naturality of `finalPullbackUnit` in the module — what is left is the cocycle
`AlgebraicGeometry.SmallEtale.smallEtalePullbackFactoredCompIso_assoc` of Stacks 021J at
`k ≫ w = w'`, `w ≫ f = g`. -/
public theorem sectionsSheafTauRho_naturality
    {W W' : SmallEtale B T.left.obj T.left.property} (k : W' ⟶ W)
    (g : W.obj.left ⟶ B.obj S hS) (hg : W.obj.hom ≫ T.hom = g)
    (g' : W'.obj.left ⟶ B.obj S hS) (hg' : W'.obj.hom ≫ T.hom = g')
    (habc : k.hom.left ≫ g = g') :
    (sectionsSheafTauPullback B S hS 𝓖 T).val.presheaf.map k.op ≫
        sectionsSheafTauRho B S hS 𝓖 T W' g' hg' =
      sectionsSheafTauRho B S hS 𝓖 T W g hg ≫
        (finalPullbackUnit B k.hom.left
            ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B g)).obj 𝓖) ≫
          smallEtaleSectionsApp B
            ((smallEtalePullbackFactoredCompIso B k.hom.left g g' habc).hom.app 𝓖)
            (final B W'.obj.left.obj W'.obj.left.property)) := by
  have hloc := sectionsSheafTauLocApp_naturality B T.left.obj T.left.property
    (sectionsSheafTauPullback B S hS 𝓖 T) k
  simp only [sectionsSheafTauRho, Category.assoc]
  slice_lhs 1 2 => rw [hloc]
  simp only [sectionsSheafTauMap, Category.assoc]
  slice_rhs 2 4 => rw [sectionsApp_pullbackUnit_cocycle B S hS 𝓖 k.hom.left W.obj.hom T.hom g hg
    W'.obj.hom (Over.w k.hom) g' habc hg']

end Restricted


/-! ### The functor presenting `i_T` of Stacks 021F -/

section ITFunctor

variable (T : BigEtaleOver B S hS)

/-- **The functor presenting `i_T` of Stacks 021F**: an étale `W / T` is sent to `W / S`. -/
public abbrev smallEtaleToBigOver :
    SmallEtale B T.left.obj T.left.property ⥤ BigEtaleOver B S hS :=
  inclusion B T.left.obj T.left.property ⋙ Over.map T.hom

/-- **`i_T^{-1}𝒪 = 𝒪`.**  Restricting the structure presheaf of the big étale category over `S`
along the functor presenting `i_T` returns the structure presheaf of the small étale site of the
scheme of `T`: both are global functions on the underlying scheme, and `Over.map` leaves the
total space untouched, so this is the identity.  This is the content of
`AlgebraicGeometry.smallEtaleToBig_structureSheaf`. -/
public def smallEtaleToBigOverRingMap :
    (structureSheaf B T.left.obj T.left.property).obj ⟶
      (smallEtaleToBigOver B S hS T).op ⋙ bigEtaleOverRing B S hS :=
  𝟙 _

/-- **The projection `T ×_S V / S ⟶ V / S`**, for an étale `V / S`: the comparison
`i_T ∘ f_small ⟹ i_S` whose existence is what makes `f_small` factor through `i_T` in
Stacks 021I (4). -/
public def nuProj (V : SmallEtale B S hS) :
    (smallEtaleToBigOver B S hS T).obj ((smallEtaleBaseChange B T.hom).obj V) ⟶
      (inclusion B S hS).obj V :=
  Over.homMk (Limits.pullback.fst V.obj.hom T.hom) Limits.pullback.condition

/-- `AlgebraicGeometry.SmallEtale.nuProj` is natural in `V`.  On underlying morphisms of schemes
this is `AlgebraicGeometry.smallEtaleBaseChange_map_hom_left_comp_fst`, the statement that base
change commutes with the projection upstairs. -/
public theorem nuProj_naturality {V V' : SmallEtale B S hS} (k : V' ⟶ V) :
    (smallEtaleToBigOver B S hS T).map ((smallEtaleBaseChange B T.hom).map k) ≫
        nuProj B S hS T V =
      nuProj B S hS T V' ≫ (inclusion B S hS).map k :=
  Over.OverMorphism.ext (smallEtaleBaseChange_map_hom_left_comp_fst B T.hom k)

/-! ### The generator identity for the comparison `ρ'` -/

/-- **The two arrows into the base change along `T ×_S V → S` agree.**  On the left the diagonal
of `T ×_S V` followed by the comparison of **Stacks 021J** for the factorization through `T`; on
the right the canonical arrow into the base change of the final object, the base change of the
diagonal of `V`, and the comparison for the factorization through `V`.

Both are morphisms into a base change along `T ×_S V → S`, so by
`AlgebraicGeometry.SmallEtale.hom_ext_of_comp_fst_smallEtaleBaseChange` it suffices to compose
with the projection to `V` upstairs, and the projection identities of Stacks 021J together with
`AlgebraicGeometry.SmallEtale.finalToSelfBaseChange_left_comp_fst` and
`AlgebraicGeometry.SmallEtale.terminalFrom_final_hom_left_comp_fst` carry both to the projection
`T ×_S V ⟶ V`.  This is the only geometric input to
`AlgebraicGeometry.SmallEtale.sectionsSheafTauRho_unitSectionsApp`. -/
public theorem finalToSelfBaseChange_comp_factoredCompIso_eq (V : SmallEtale B S hS)
    (hq : (nuProj B S hS T V).left ≫ V.obj.hom =
      ((smallEtaleBaseChange B T.hom).obj V).obj.hom ≫ T.hom) :
    (finalToSelfBaseChange ((smallEtaleBaseChange B T.hom).obj V) ≫
        (smallEtaleBaseChange_factoredCompIso B _ _ _
          ((smallEtaleBaseChange B T.hom).obj V).obj.hom T.hom
          (((smallEtaleBaseChange B T.hom).obj V).obj.hom ≫ T.hom) rfl).hom.app V) =
      ((((smallEtaleBaseChange_finalIsTerminal B (nuProj B S hS T V).left).from
          (final B ((smallEtaleBaseChange B T.hom).obj V).obj.left.obj
            ((smallEtaleBaseChange B T.hom).obj V).obj.left.property)) ≫
          (smallEtaleBaseChange B (nuProj B S hS T V).left).map (finalToSelfBaseChange V)) ≫
        (smallEtaleBaseChange_factoredCompIso B _ _ _
          (nuProj B S hS T V).left V.obj.hom
          (((smallEtaleBaseChange B T.hom).obj V).obj.hom ≫ T.hom) hq).hom.app V) := by
  refine hom_ext_of_comp_fst_smallEtaleBaseChange B
    (((smallEtaleBaseChange B T.hom).obj V).obj.hom ≫ T.hom) _ _ ?_
  have hLl : (finalToSelfBaseChange ((smallEtaleBaseChange B T.hom).obj V)).hom.left ≫
        ((smallEtaleBaseChange_factoredCompIso B _ _ _
        ((smallEtaleBaseChange B T.hom).obj V).obj.hom T.hom
          (((smallEtaleBaseChange B T.hom).obj V).obj.hom ≫ T.hom) rfl).hom.app V).hom.left ≫
          Limits.pullback.fst V.obj.hom
            (((smallEtaleBaseChange B T.hom).obj V).obj.hom ≫ T.hom) =
      Limits.pullback.fst V.obj.hom T.hom :=
    (congrArg (fun t => (finalToSelfBaseChange
            ((smallEtaleBaseChange B T.hom).obj V)).hom.left ≫ t)
        (smallEtaleBaseChange_factoredCompIso_hom_app_fst B _ _ _
          ((smallEtaleBaseChange B T.hom).obj V).obj.hom T.hom
          (((smallEtaleBaseChange B T.hom).obj V).obj.hom ≫ T.hom) rfl V)).trans
      (finalToSelfBaseChange_left_comp_fst_comp ((smallEtaleBaseChange B T.hom).obj V)
        (Limits.pullback.fst V.obj.hom T.hom))
  have hRl := terminalFrom_comp_map_finalToSelfBaseChange_comp_fst V (nuProj B S hS T V).left
    _ hq
  simp only [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left, Category.assoc]
  exact ((Category.assoc _ _ _).trans hLl).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun t => ((smallEtaleBaseChange_finalIsTerminal B (nuProj B S hS T V).left).from
            (final B ((smallEtaleBaseChange B T.hom).obj V).obj.left.obj
              ((smallEtaleBaseChange B T.hom).obj V).obj.left.property)).hom.left ≫ t)
          (Category.assoc _ _ _)).trans hRl)).symm

/-- **The generator identity of Stacks 070S part (3).**  On the image under the unit along `ε_f`
of a section of `𝓖` over an étale `V / S`, the comparison
`AlgebraicGeometry.SmallEtale.sectionsSheafTauRho` at the base change `T ×_S V` is the
localization map at `V` followed by restriction along the projection `T ×_S V / S ⟶ V / S` of
Stacks 021I (4).

Both sides are a *two-step* unit — on the left along `T ×_S V → T` and then `T → S`, on the
right along `T ×_S V → V` and then `V → S` — followed by a restriction, and
`AlgebraicGeometry.SmallEtale.unitSectionsApp_factoredComp_obj_comp` contracts each into the
*one-step* unit along `T ×_S V → S` followed by a restriction.  What is left is that the two
resulting arrows `T ×_S V / (T ×_S V) ⟶ (T ×_S V) ×_S V` agree, and both are morphisms into a
base change, so `AlgebraicGeometry.SmallEtale.hom_ext_of_comp_fst_smallEtaleBaseChange` reduces
that to the projection upstairs, where both sides become the projection
`T ×_S V ⟶ V`. -/
public theorem sectionsSheafTauRho_unitSectionsApp (V : SmallEtale B S hS) :
    unitSectionsApp B T.hom 𝓖 V ≫
        sectionsSheafTauRho B S hS 𝓖 T ((smallEtaleBaseChange B T.hom).obj V)
          (((smallEtaleBaseChange B T.hom).obj V).obj.hom ≫ T.hom) rfl =
      sectionsSheafTauLocApp B S hS 𝓖 V ≫
        sectionsSheafTauMap B S hS 𝓖 (nuProj B S hS T V) := by
  have hq : (nuProj B S hS T V).left ≫ V.obj.hom =
      ((smallEtaleBaseChange B T.hom).obj V).obj.hom ≫ T.hom :=
    Over.w (nuProj B S hS T V)
  have hcL : (finalToSelfBaseChange ((smallEtaleBaseChange B T.hom).obj V) ≫
      (smallEtaleBaseChange_factoredCompIso B _ _ _
          ((smallEtaleBaseChange B T.hom).obj V).obj.hom T.hom
            (((smallEtaleBaseChange B T.hom).obj V).obj.hom ≫ T.hom) rfl).hom.app V) ≫
            (smallEtaleBaseChange_factoredCompIso B _ _ _
          ((smallEtaleBaseChange B T.hom).obj V).obj.hom T.hom
            (((smallEtaleBaseChange B T.hom).obj V).obj.hom ≫ T.hom) rfl).inv.app V =
      finalToSelfBaseChange ((smallEtaleBaseChange B T.hom).obj V) := by
    rw [Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id _
  have hcR : ((((smallEtaleBaseChange_finalIsTerminal B (nuProj B S hS T V).left).from
        (final B ((smallEtaleBaseChange B T.hom).obj V).obj.left.obj
          ((smallEtaleBaseChange B T.hom).obj V).obj.left.property)) ≫
        (smallEtaleBaseChange B (nuProj B S hS T V).left).map (finalToSelfBaseChange V)) ≫
          (smallEtaleBaseChange_factoredCompIso B _ _ _
          (nuProj B S hS T V).left V.obj.hom (((smallEtaleBaseChange B T.hom).obj V).obj.hom ≫
            T.hom) hq).hom.app V) ≫ (smallEtaleBaseChange_factoredCompIso B _ _ _
          (nuProj B S hS T V).left V.obj.hom (((smallEtaleBaseChange B T.hom).obj V).obj.hom ≫
            T.hom) hq).inv.app V = (((smallEtaleBaseChange_finalIsTerminal B
            (nuProj B S hS T V).left).from
        (final B ((smallEtaleBaseChange B T.hom).obj V).obj.left.obj
          ((smallEtaleBaseChange B T.hom).obj V).obj.left.property)) ≫
        (smallEtaleBaseChange B (nuProj B S hS T V).left).map (finalToSelfBaseChange V)) := by
    rw [Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id _
  have hL := unitSectionsApp_factoredComp_obj_comp
    ((smallEtaleBaseChange B T.hom).obj V).obj.hom T.hom
    (((smallEtaleBaseChange B T.hom).obj V).obj.hom ≫ T.hom) rfl 𝓖 V
    (final B ((smallEtaleBaseChange B T.hom).obj V).obj.left.obj
      ((smallEtaleBaseChange B T.hom).obj V).obj.left.property) (finalToSelfBaseChange
        ((smallEtaleBaseChange B T.hom).obj V) ≫ (smallEtaleBaseChange_factoredCompIso B _ _ _
          ((smallEtaleBaseChange B T.hom).obj V).obj.hom T.hom
            (((smallEtaleBaseChange B T.hom).obj V).obj.hom ≫ T.hom) rfl).hom.app V)
  have hR := unitSectionsApp_factoredComp_obj_comp
    (nuProj B S hS T V).left V.obj.hom
    (((smallEtaleBaseChange B T.hom).obj V).obj.hom ≫ T.hom) hq 𝓖 V
    (final B ((smallEtaleBaseChange B T.hom).obj V).obj.left.obj
      ((smallEtaleBaseChange B T.hom).obj V).obj.left.property)
        ((((smallEtaleBaseChange_finalIsTerminal B (nuProj B S hS T V).left).from
        (final B ((smallEtaleBaseChange B T.hom).obj V).obj.left.obj
          ((smallEtaleBaseChange B T.hom).obj V).obj.left.property)) ≫
        (smallEtaleBaseChange B (nuProj B S hS T V).left).map (finalToSelfBaseChange V)) ≫
          (smallEtaleBaseChange_factoredCompIso B _ _ _
          (nuProj B S hS T V).left V.obj.hom (((smallEtaleBaseChange B T.hom).obj V).obj.hom ≫
            T.hom) hq).hom.app V)
  rw [hcL] at hL
  rw [hcR] at hR
  rw [finalToSelfBaseChange_comp_factoredCompIso_eq B S hS T V hq] at hL
  have hnat := unitSectionsApp_naturality_obj B (nuProj B S hS T V).left
    ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B V.obj.hom)).obj 𝓖)
    (finalToSelfBaseChange V)
  simp only [sectionsSheafTauRho, sectionsSheafTauLocApp, sectionsSheafTauMap,
    finalPullbackUnit, Category.assoc]
  slice_rhs 2 3 => rw [hnat]
  slice_rhs 3 4 => rw [← CategoryTheory.Functor.map_comp, ← op_comp]
  exact hL.trans hR.symm

/-- **The bijection `Hom_S(W, V) ≅ Hom_T(W, T ×_S V)`**, in the direction needed: a morphism
`W / S ⟶ V / S` of the big category over `S`, out of an object of the small étale site of the
scheme of `T`, is the projection of a morphism `W ⟶ T ×_S V` of that small étale site. -/
public def kappaLift (V : SmallEtale B S hS)
    {W : SmallEtale B T.left.obj T.left.property}
    (g : (smallEtaleToBigOver B S hS T).obj W ⟶ (inclusion B S hS).obj V) :
    W ⟶ (smallEtaleBaseChange B T.hom).obj V :=
  ObjectProperty.homMk (Over.homMk (Limits.pullback.lift g.left W.obj.hom (Over.w g))
    (Limits.pullback.lift_snd _ _ _))

/-- `AlgebraicGeometry.SmallEtale.kappaLift` does lift: composing it with the projection
`T ×_S V / S ⟶ V / S` of Stacks 021I (4) returns the given morphism. -/
public theorem kappaLift_spec (V : SmallEtale B S hS)
    {W : SmallEtale B T.left.obj T.left.property}
    (g : (smallEtaleToBigOver B S hS T).obj W ⟶ (inclusion B S hS).obj V) :
    (smallEtaleToBigOver B S hS T).map (kappaLift B S hS T V g) ≫ nuProj B S hS T V = g :=
  Over.OverMorphism.ext (Limits.pullback.lift_fst _ _ _)

/-- **The canonical isomorphism `i_T(T/T) ≅ T`.**  The functor presenting `i_T` sends the final
object of the small étale site of the scheme of `T` to `T` with its structure morphism
precomposed with the identity. -/
public def finalOverIso :
    (smallEtaleToBigOver B S hS T).obj (final B T.left.obj T.left.property) ≅ T :=
  Over.isoMk (Iso.refl _) (Category.id_comp _)

/-- **At the final object, `ρ'` for the factorization `𝟙 ≫ f` is restriction along the canonical
isomorphism `i_T(T/T) ≅ T`.**  By
`AlgebraicGeometry.SmallEtale.sectionsSheafTauRho_naturality` at the identity it is `ρ'` for the
factorization `f` followed by that restriction, and the first factor is the identity by
`AlgebraicGeometry.SmallEtale.sectionsSheafTauRho_final`. -/
public theorem sectionsSheafTauRho_app_final :
    sectionsSheafTauRho B S hS 𝓖 T (final B T.left.obj T.left.property)
        ((final B T.left.obj T.left.property).obj.hom ≫ T.hom) rfl =
      sectionsSheafTauMap B S hS 𝓖 (finalOverIso B S hS T).hom := by
  have hg : (final B T.left.obj T.left.property).obj.hom ≫ T.hom = T.hom :=
    Category.id_comp _
  have hnat := sectionsSheafTauRho_naturality B S hS 𝓖 T
    (𝟙 (final B T.left.obj T.left.property)) T.hom hg
    ((final B T.left.obj T.left.property).obj.hom ≫ T.hom) rfl rfl
  rw [sectionsSheafTauRho_final B S hS 𝓖 T hg] at hnat
  refine Eq.trans (Category.id_comp _).symm ?_
  refine Eq.trans (congrArg (fun t : sectionsSheafTauObj B S hS 𝓖 T ⟶
        sectionsSheafTauObj B S hS 𝓖 T =>
      t ≫ sectionsSheafTauRho B S hS 𝓖 T (final B T.left.obj T.left.property)
        ((final B T.left.obj T.left.property).obj.hom ≫ T.hom) rfl)
    ((sectionsSheafTauPullback B S hS 𝓖 T).val.presheaf.map_id
      (op (final B T.left.obj T.left.property))).symm) ?_
  exact hnat.trans (Category.id_comp _)

/-- `AlgebraicGeometry.SmallEtale.sectionsSheafTauRho_app_final` read on sections. -/
public theorem sectionsSheafTauRho_app_final_apply
    (y : (sectionsSheafTauPullback B S hS 𝓖 T).val.presheaf.obj
      (op (final B T.left.obj T.left.property))) :
    sectionsSheafTauRho B S hS 𝓖 T (final B T.left.obj T.left.property)
        ((final B T.left.obj T.left.property).obj.hom ≫ T.hom) rfl y =
      sectionsSheafTauMap B S hS 𝓖 (finalOverIso B S hS T).hom y :=
  CategoryTheory.congr_fun (sectionsSheafTauRho_app_final B S hS 𝓖 T) y

end ITFunctor


/-! ### Restriction of presheaves of modules along a natural transformation of site functors -/

namespace PushforwardNat

variable {A : Type*} [Category* A] {Cc : Type*} [Category* Cc]
  {j k : A ⥤ Cc} (ν : j ⟶ k)
  {RA : Aᵒᵖ ⥤ RingCat.{u}} {RC : Ccᵒᵖ ⥤ RingCat.{u}}
  (α : RA ⟶ j.op ⋙ RC) (β : RA ⟶ k.op ⋙ RC)
  (h : ∀ X : Aᵒᵖ, β.app X ≫ RC.map (ν.app X.unop).op = α.app X)
  (M : PresheafOfModules.{u} RC)

/-- **Restriction of a presheaf of modules along a natural transformation of site functors.**
For `ν : j ⟶ k` between functors `A ⥤ Cc` and structure maps `α`, `β` for `j` and `k` whose
difference is restriction along `ν`, the restriction maps of `M` along the components of `ν`
assemble into a morphism `k_*M ⟶ j_*M` of presheaves of `RA`-modules.

Linearity at `X` is exactly the compatibility `h`: a scalar acts on the source through `β` and
on the target through `α`, and `PresheafOfModules.map_smul` turns the first into the second.
Naturality is naturality of `ν` read under `M`.  Mathlib has `pushforward` functorial in the
module and `pushforwardComp` for a composite of functors, but nothing for a natural
transformation of the functors; this is that. -/
public def pushforwardNatTrans :
    (PresheafOfModules.pushforward.{u} β).obj M ⟶
      (PresheafOfModules.pushforward.{u} α).obj M where
  app X := ModuleCat.homEquiv.symm
    { toFun := fun m => M.map (ν.app X.unop).op m
      map_add' := fun a b => map_add (M.map (ν.app X.unop).op).hom a b
      map_smul' := fun r m => by
        refine Eq.trans (M.map_smul (ν.app X.unop).op ((β.app X).hom r) m) ?_
        exact congrArg (fun s => s • M.map (ν.app X.unop).op m)
          (congrFun (congrArg (fun t : (_ : RingCat.{u}) ⟶ _ => t.hom.toFun) (h X)) r) }
  naturality {X Y} f := by
    ext m
    refine Eq.trans (M.map_comp_apply _ _ m).symm
      (Eq.trans ?_ (M.map_comp_apply _ _ m))
    exact (congrArg (fun t : j.obj Y.unop ⟶ k.obj X.unop =>
      M.map (Quiver.Hom.op t) m) (ν.naturality f.unop)).symm

/-- **`AlgebraicGeometry.SmallEtale.PushforwardNat.pushforwardNatTrans` is natural in the
module.**  Both composites are, at an object, the restriction map of the target along the
component of `ν` precomposed with the morphism, and that is the naturality of the morphism. -/
public theorem pushforwardNatTrans_naturality {M' : PresheafOfModules.{u} RC} (f : M ⟶ M') :
    pushforwardNatTrans ν α β h M ≫ (PresheafOfModules.pushforward.{u} α).map f =
      (PresheafOfModules.pushforward.{u} β).map f ≫ pushforwardNatTrans ν α β h M' := by
  ext X x
  exact PresheafOfModules.naturality_apply f (ν.app X.unop).op x

end PushforwardNat


/-! ### The comparison `θ` with the inverse image sheaf -/

section Theta

variable (T : BigEtaleOver B S hS)

/-- The presheaf-level inverse image of `𝓖` along `ε_f`, on the small étale site of the scheme
of `T / S`.  Its `T_étale`-sheafification is `f_small^*𝓖`, by
`CategoryTheory.SheafOfModules.pullbackIso`. -/
public abbrev sectionsSheafTauPresheafPullback :
    PresheafOfModules.{u} (structureSheaf B T.left.obj T.left.property).obj :=
  (PresheafOfModules.pullback.{u} (smallEtaleStructureMapRing B T.hom).hom).obj 𝓖.val

/-- **θ**: the comparison from the presheaf-level inverse image of `𝓖` along `ε_f` to the sheaf
`f_small^*𝓖`, namely the transpose, along the adjunction for presheaves of modules, of the unit
of `ε_f^* ⊣ ε_{f,*}` for sheaves of modules. -/
public def sectionsSheafTauTheta :
    sectionsSheafTauPresheafPullback B S hS 𝓖 T ⟶ (sectionsSheafTauPullback B S hS 𝓖 T).val :=
  ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
      (smallEtaleStructureMapRing B T.hom).hom).homEquiv _ _).symm
    ((SheafOfModules.pullbackPushforwardAdjunction.{u}
      (smallEtaleStructureMapRing B T.hom)).unit.app 𝓖).val

/-- **θ's transpose is the unit of `ε_f^* ⊣ ε_{f,*}` for sheaves of modules**, which is how `θ`
is defined. -/
public theorem homEquiv_sectionsSheafTauTheta :
    ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
        (smallEtaleStructureMapRing B T.hom).hom).homEquiv _ _)
        (sectionsSheafTauTheta B S hS 𝓖 T) =
      ((SheafOfModules.pullbackPushforwardAdjunction.{u}
        (smallEtaleStructureMapRing B T.hom)).unit.app 𝓖).val :=
  Equiv.apply_symm_apply _ _

/-- **The unit of `CategoryTheory.SheafOfModules.PullbackConstruction.adjunction` is the
transpose of the sheafification unit.**  That adjunction presents `ε_f^*` on sheaves of modules
as the presheaf-level inverse image followed by sheafification, and it is built from its hom-set
bijection, so its unit is read off `CategoryTheory.Adjunction.mkOfHomEquiv_unit_app`. -/
public theorem pullbackConstruction_unit_app_val :
    ((SheafOfModules.PullbackConstruction.adjunction.{u}
        (smallEtaleStructureMapRing B T.hom)).unit.app 𝓖).val =
      ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
          (smallEtaleStructureMapRing B T.hom).hom).homEquiv _ _)
        ((PresheafOfModules.sheafificationAdjunction.{u}
            (𝟙 (structureSheaf B T.left.obj T.left.property).obj)).unit.app
          (sectionsSheafTauPresheafPullback B S hS 𝓖 T)) := by
  simp only [SheafOfModules.PullbackConstruction.adjunction,
    Adjunction.mkOfHomEquiv_unit_app, Adjunction.homEquiv_unit]
  rfl

/-- **θ is the sheafification unit followed by an isomorphism.**  The sheafification unit of the
presheaf-level inverse image of `𝓖` along `ε_f`, followed by the inverse of
`CategoryTheory.SheafOfModules.pullbackIso` — which presents `ε_f^*𝓖` as that sheafification —
is `AlgebraicGeometry.SmallEtale.sectionsSheafTauTheta`.

Both sides are morphisms out of a presheaf-level inverse image, so it is enough to compare their
transposes across `ε_f^{*,pre} ⊣ ε_{f,*}`.  On the left the transpose is the unit of
`ε_f^* ⊣ ε_{f,*}` for sheaves of modules, by the definition of `θ`; on the right it is the unit
of `CategoryTheory.SheafOfModules.PullbackConstruction.adjunction` followed by the comparison,
and `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` — the identity that pins
`pullbackIso` down by its effect on units — identifies the two.

Since the sheafification unit is locally bijective and the second factor is an isomorphism, this
is what makes `θ` locally bijective. -/
public theorem sectionsSheafTauTheta_eq :
    sectionsSheafTauTheta B S hS 𝓖 T =
      (PresheafOfModules.sheafificationAdjunction.{u}
          (𝟙 (structureSheaf B T.left.obj T.left.property).obj)).unit.app
            (sectionsSheafTauPresheafPullback B S hS 𝓖 T) ≫
        ((SheafOfModules.pullbackIso.{u} (smallEtaleStructureMapRing B T.hom)).inv.app 𝓖).val := by
  apply ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
    (smallEtaleStructureMapRing B T.hom).hom).homEquiv _ _).injective
  refine Eq.trans (Equiv.apply_symm_apply _ _) ?_
  refine Eq.trans (congrArg (fun k : 𝓖 ⟶ _ => k.val)
    (Adjunction.unit_leftAdjointUniq_hom_app
      (SheafOfModules.PullbackConstruction.adjunction.{u} (smallEtaleStructureMapRing B T.hom))
      (SheafOfModules.pullbackPushforwardAdjunction.{u}
        (smallEtaleStructureMapRing B T.hom)) 𝓖).symm) ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_naturality_right _ _ _).symm
  exact congrArg (fun t => t ≫ (PresheafOfModules.pushforward.{u}
    (smallEtaleStructureMapRing B T.hom).hom).map _)
    (pullbackConstruction_unit_app_val B S hS 𝓖 T)

/-- **θ is locally surjective** for the étale topology on the small étale site of the scheme of
`T`: it is the sheafification unit, which is locally bijective, followed by an isomorphism. -/
public instance isLocallySurjective_sectionsSheafTauTheta :
    Presheaf.IsLocallySurjective (topology B T.left.obj T.left.property)
      ((PresheafOfModules.toPresheaf
        (structureSheaf B T.left.obj T.left.property).obj).map
          (sectionsSheafTauTheta B S hS 𝓖 T)) := by
  have hiso : IsIso ((PresheafOfModules.toPresheaf
      (structureSheaf B T.left.obj T.left.property).obj).map ((SheafOfModules.pullbackIso.{u}
        (smallEtaleStructureMapRing B T.hom)).inv.app 𝓖).val) :=
    inferInstanceAs (IsIso ((SheafOfModules.forget
        (structureSheaf B T.left.obj T.left.property) ⋙
      PresheafOfModules.toPresheaf (structureSheaf B T.left.obj T.left.property).obj).map
        ((SheafOfModules.pullbackIso.{u} (smallEtaleStructureMapRing B T.hom)).inv.app 𝓖)))
  have h3 : Presheaf.IsLocallySurjective (topology B T.left.obj T.left.property)
      ((PresheafOfModules.toPresheaf
        (structureSheaf B T.left.obj T.left.property).obj).map ((SheafOfModules.pullbackIso.{u}
          (smallEtaleStructureMapRing B T.hom)).inv.app 𝓖).val) :=
    inferInstance
  have h1 : Presheaf.IsLocallySurjective (topology B T.left.obj T.left.property)
      ((PresheafOfModules.toPresheaf
        (structureSheaf B T.left.obj T.left.property).obj).map
          ((PresheafOfModules.sheafificationAdjunction.{u}
            (𝟙 (structureSheaf B T.left.obj T.left.property).obj)).unit.app
              (sectionsSheafTauPresheafPullback B S hS 𝓖 T))) := by
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact (GrothendieckTopology.W_toSheafify _ _).isLocallySurjective
  have hsplit : (PresheafOfModules.toPresheaf
        (structureSheaf B T.left.obj T.left.property).obj).map
          (sectionsSheafTauTheta B S hS 𝓖 T) =
      (PresheafOfModules.toPresheaf
          (structureSheaf B T.left.obj T.left.property).obj).map
            ((PresheafOfModules.sheafificationAdjunction.{u}
              (𝟙 (structureSheaf B T.left.obj T.left.property).obj)).unit.app
                (sectionsSheafTauPresheafPullback B S hS 𝓖 T)) ≫
        (PresheafOfModules.toPresheaf
          (structureSheaf B T.left.obj T.left.property).obj).map ((SheafOfModules.pullbackIso.{u}
            (smallEtaleStructureMapRing B T.hom)).inv.app 𝓖).val :=
    (congrArg (fun t : sectionsSheafTauPresheafPullback B S hS 𝓖 T ⟶
          (sectionsSheafTauPullback B S hS 𝓖 T).val =>
        (PresheafOfModules.toPresheaf
          (structureSheaf B T.left.obj T.left.property).obj).map t)
      (sectionsSheafTauTheta_eq B S hS 𝓖 T)).trans (Functor.map_comp _ _ _)
  exact hsplit ▸ (@Presheaf.isLocallySurjective_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h3)

/-- **θ is locally injective** for the étale topology on the small étale site of the scheme of
`T`, for the same reason as
`AlgebraicGeometry.SmallEtale.isLocallySurjective_sectionsSheafTauTheta`. -/
public instance isLocallyInjective_sectionsSheafTauTheta :
    Presheaf.IsLocallyInjective (topology B T.left.obj T.left.property)
      ((PresheafOfModules.toPresheaf
        (structureSheaf B T.left.obj T.left.property).obj).map
          (sectionsSheafTauTheta B S hS 𝓖 T)) := by
  have hiso : IsIso ((PresheafOfModules.toPresheaf
      (structureSheaf B T.left.obj T.left.property).obj).map ((SheafOfModules.pullbackIso.{u}
        (smallEtaleStructureMapRing B T.hom)).inv.app 𝓖).val) :=
    inferInstanceAs (IsIso ((SheafOfModules.forget
        (structureSheaf B T.left.obj T.left.property) ⋙
      PresheafOfModules.toPresheaf (structureSheaf B T.left.obj T.left.property).obj).map
        ((SheafOfModules.pullbackIso.{u} (smallEtaleStructureMapRing B T.hom)).inv.app 𝓖)))
  have h3 : Presheaf.IsLocallyInjective (topology B T.left.obj T.left.property)
      ((PresheafOfModules.toPresheaf
        (structureSheaf B T.left.obj T.left.property).obj).map ((SheafOfModules.pullbackIso.{u}
          (smallEtaleStructureMapRing B T.hom)).inv.app 𝓖).val) :=
    inferInstance
  have h1 : Presheaf.IsLocallyInjective (topology B T.left.obj T.left.property)
      ((PresheafOfModules.toPresheaf
        (structureSheaf B T.left.obj T.left.property).obj).map
          ((PresheafOfModules.sheafificationAdjunction.{u}
            (𝟙 (structureSheaf B T.left.obj T.left.property).obj)).unit.app
              (sectionsSheafTauPresheafPullback B S hS 𝓖 T))) := by
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact (GrothendieckTopology.W_toSheafify _ _).isLocallyInjective
  have hsplit : (PresheafOfModules.toPresheaf
        (structureSheaf B T.left.obj T.left.property).obj).map
          (sectionsSheafTauTheta B S hS 𝓖 T) =
      (PresheafOfModules.toPresheaf
          (structureSheaf B T.left.obj T.left.property).obj).map
            ((PresheafOfModules.sheafificationAdjunction.{u}
              (𝟙 (structureSheaf B T.left.obj T.left.property).obj)).unit.app
                (sectionsSheafTauPresheafPullback B S hS 𝓖 T)) ≫
        (PresheafOfModules.toPresheaf
          (structureSheaf B T.left.obj T.left.property).obj).map ((SheafOfModules.pullbackIso.{u}
            (smallEtaleStructureMapRing B T.hom)).inv.app 𝓖).val :=
    (congrArg (fun t : sectionsSheafTauPresheafPullback B S hS 𝓖 T ⟶
          (sectionsSheafTauPullback B S hS 𝓖 T).val =>
        (PresheafOfModules.toPresheaf
          (structureSheaf B T.left.obj T.left.property).obj).map t)
      (sectionsSheafTauTheta_eq B S hS 𝓖 T)).trans (Functor.map_comp _ _ _)
  exact hsplit ▸ (@Presheaf.isLocallyInjective_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h3)

end Theta

end AlgebraicGeometry.SmallEtale

end

