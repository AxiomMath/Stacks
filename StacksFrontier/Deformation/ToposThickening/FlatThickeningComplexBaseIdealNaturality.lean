module

public import StacksFrontier.Deformation.ToposThickening.FlatThickeningComplexBaseIdealTranspose

/-!
# The maps `f^*𝒥₂ ⟶ f^*𝒥₁` induced by a morphism of thickenings of the base

For a morphism `E` of first order thickenings of a ringed topos `(Sh(B), O_ℬ)` presented on one
site, with defining ideals `𝒥₂ ⟶ 𝒥₁`, this file constructs the induced map `t₂^*𝒥₂ ⟶ t₁^*𝒥₁`
of `O_ℬ`-modules (the transpose along `t₂^* ⊣ t₂_*` of `𝒥₂ ⟶ 𝒥₁` followed by the unit
`𝒥₁ ⟶ t_*t₁^*𝒥₁`) and its pullback `f^*𝒥₂ ⟶ f^*𝒥₁` along `f : (Sh(C), O) ⟶ (Sh(B), O_ℬ)`.

Over a morphism `U` of first order thickenings of `(Sh(C), O)` and two strict flat deformations
`f'₁, f'₂` of `f` forming a commutative square with the horizontal arrows, it proves that the
induced map is the map `I₂ ⟶ I₁` of `U` read through the identifications `f^*𝒥ₖ = Iₖ` of
Situation 08VV (`Deformation.ToposThickening.basePullbackIdealIsoIdeal`), as Stacks 08VT does on
ringed spaces. Both maps are compared after the inclusion `I₁ ⊂ O'₁`, the reduction
`f'₂^*𝒥₂ ⟶ i₂_*f^*𝒥₂` (an epimorphism) and the transposition along `f'₂^* ⊣ f'₂_*`: there both
become the structure map of `f'₂` on `𝒥₂` followed by `h^♯`, which is checked on underlying
sheaves of sets, where the two columns have the same direct images.

## Main definitions

* `Deformation.ToposThickening.FirstOrderThickening.idealToPushforwardPullback`: the unit
  `𝒥 ⟶ t_*t^*𝒥` of the defining ideal, as a map of modules over `t_*O_ℬ`.
* `Deformation.ToposThickening.MorphismOfFirstOrderThickenings.pullbackIdealMap`: the induced map
  `t₂^*𝒥₂ ⟶ t₁^*𝒥₁`.
* `Deformation.ToposThickening.basePullbackIdealMap`: its pullback `f^*𝒥₂ ⟶ f^*𝒥₁`, and
  `Deformation.ToposThickening.basePullbackIdealOverThickenedMap`, the same map read over `i_*O`.

## Main results

* `Deformation.ToposThickening.homThroughIsos_basePullbackIdealIsoIdeal_idealMap`: the map
  `I₂ ⟶ I₁`, read through the identifications `f^*𝒥ₖ = Iₖ`, is the induced map
  `f^*𝒥₂ ⟶ f^*𝒥₁`.

## References

* [Stacks Project, Tag 08VY](https://stacks.math.columbia.edu/tag/08VY)
* [Stacks Project, Tag 08VT](https://stacks.math.columbia.edu/tag/08VT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

universe v u w v₂ u₂ vB uB wB vB' uB' wB'

namespace Deformation.ToposThickening

namespace FirstOrderThickening

variable {B : RingedTopos.{vB, uB, wB}} {B' : RingedTopos.{vB', uB', wB'}}
  [B.J.HasSheafCompose (forget RingCat.{wB})] [B'.J.HasSheafCompose (forget RingCat.{wB'})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{wB} RingCat.{wB})]
  [B'.J.HasSheafCompose (forget₂ CommRingCat.{wB'} RingCat.{wB'})]
  [B.J.HasSheafCompose (forget AddCommGrpCat.{wB})]
  [B'.J.HasSheafCompose (forget AddCommGrpCat.{wB'})]
  [HasWeakSheafify B.J AddCommGrpCat.{wB}] [B.J.WEqualsLocallyBijective AddCommGrpCat.{wB}]
  {t : RingedToposHom B B'} (ht : FirstOrderThickening t)

/-- The unit `𝒥 ⟶ t_*t^*𝒥` of the defining ideal of a first order thickening, as a map of modules
over `t_*O_ℬ`: restriction of scalars along `O_{ℬ'} ⟶ t_*O_ℬ` is fully faithful. -/
noncomputable def idealToPushforwardPullback :
    ht.I ⟶ (pushforwardModuleFunctor t.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf B.O)).obj
      ((pullbackModules t.toRingedToposModulesHom).obj ht.idealOfThickening.I) :=
  ht.restrictScalarsFullyFaithful.preimage
    (t.pullbackAdjPushforwardModulesViaComparison.unit.app ht.idealOfThickening.I)

/-- The unit `𝒥 ⟶ t_*t^*𝒥`, read over `O_{ℬ'}`, is the unit of `t^* ⊣ t_*`. -/
theorem restrictScalars_map_idealToPushforwardPullback :
    (SheafOfModules.restrictScalars (structureRingMap t)).map ht.idealToPushforwardPullback =
      t.pullbackAdjPushforwardModulesViaComparison.unit.app ht.idealOfThickening.I :=
  ht.restrictScalarsFullyFaithful.map_preimage _

end FirstOrderThickening

namespace MorphismOfFirstOrderThickenings

variable {B : RingedTopos.{vB, uB, wB}} {B' : RingedTopos.{vB', uB', wB'}}
  [B.J.HasSheafCompose (forget RingCat.{wB})] [B'.J.HasSheafCompose (forget RingCat.{wB'})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{wB} RingCat.{wB})]
  [B'.J.HasSheafCompose (forget₂ CommRingCat.{wB'} RingCat.{wB'})]
  [B.J.HasSheafCompose (forget AddCommGrpCat.{wB})]
  [B'.J.HasSheafCompose (forget AddCommGrpCat.{wB'})]
  [HasWeakSheafify B.J AddCommGrpCat.{wB}] [B.J.WEqualsLocallyBijective AddCommGrpCat.{wB}]
  {t : RingedToposHom B B'} (E : MorphismOfFirstOrderThickenings t)

/-- **The map `t₂^*𝒥₂ ⟶ t₁^*𝒥₁` induced by `𝒥₂ ⟶ 𝒥₁`**: the transpose along `t₂^* ⊣ t₂_*` of
`𝒥₂ ⟶ 𝒥₁ ⟶ t_*t₁^*𝒥₁`, read over `O_{ℬ'₂}`. -/
noncomputable def pullbackIdealMap :
    (pullbackModules (reshapeHom t E.O₂ E.fSharp₂).toRingedToposModulesHom).obj
        E.second.idealOfThickening.I ⟶
      (pullbackModules t.toRingedToposModulesHom).obj E.first.idealOfThickening.I :=
  ((reshapeHom t E.O₂ E.fSharp₂).pullbackAdjPushforwardModulesViaComparison.homEquiv _ _).symm
    ((SheafOfModules.restrictScalars (structureRingMap (reshapeHom t E.O₂ E.fSharp₂))).map
      (E.idealMap ≫ E.first.idealToPushforwardPullback))

end MorphismOfFirstOrderThickenings

section Generic

variable {𝒜 ℬ 𝒞 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒞]

/-- The image of `c : V ⟶ V₁` under `F`, transported to `A₂ ⟶ A₁` along identifications
`A₂ = F V` and `F V₁ = A₁`. -/
def mapTransport (F : ℬ ⥤ 𝒞) {V V₁ : ℬ} {A₂ A₁ : 𝒞} (α : A₂ = F.obj V) (c : V ⟶ V₁)
    (β : F.obj V₁ = A₁) : A₂ ⟶ A₁ :=
  eqToHom α ≫ F.map c ≫ eqToHom β

/-- The pullback along `F` of a transported morphism, read through transports. -/
theorem map_eqToHom_comp_comp_mapTransport {Lt : 𝒜 ⥤ ℬ} {F : ℬ ⥤ 𝒞} {J : 𝒜} {V V₁ : ℬ}
    {A₂ A₁ : 𝒞} (e : V = Lt.obj J) (ε : V ⟶ Lt.obj J) (hε : ε = eqToHom e)
    (q : (Lt ⋙ F).obj J = A₂) (g : (Lt ⋙ F).obj J ⟶ A₂) (hg : g = eqToHom q) (α : A₂ = F.obj V)
    (c : V ⟶ V₁) (β : F.obj V₁ = A₁) (d : A₂ ⟶ A₁) (hd : d = mapTransport F α c β)
    (s : F.obj V₁ ⟶ A₁) (hs : s = eqToHom β) :
    @CategoryStruct.comp _ _ (F.obj V) (F.obj (Lt.obj J)) A₁ (F.map ε)
        (@CategoryStruct.comp _ _ (F.obj (Lt.obj J)) A₂ A₁ g d) =
      F.map c ≫ s := by
  subst hε hg hd hs
  simp [mapTransport, eqToHom_map]

/-- **The transpose of a pulled-back map along a composite adjunction.** For adjunctions
`Lt ⊣ Rt`, `Lv ⊣ Rt` (two readings of one left adjoint, related on units by `ε`) and `Lf ⊣ Rf`,
the composite unit at `J` followed by `(Rf ⋙ Rt)` of `g ≫ d` is computed from a transpose `X` of
`c : Lv J ⟶ V₁` along `Lv ⊣ Rt`, provided `d` is `Lf.map c` up to the transports `ε`, `g`, `s`. -/
theorem compUnit_comp_map_eq_comp_map_unit_comp {Lt Lv : 𝒜 ⥤ ℬ} {Rt : ℬ ⥤ 𝒜} {Lf : ℬ ⥤ 𝒞}
    {Rf : 𝒞 ⥤ ℬ} (aT : Lt ⊣ Rt) (aV : Lv ⊣ Rt) (aF : Lf ⊣ Rf) {J : 𝒜} {V₁ : ℬ} {A₂ A₁ : 𝒞}
    (ε : Lv.obj J ⟶ Lt.obj J) (g : (Lt ⋙ Lf).obj J ⟶ A₂) (d : A₂ ⟶ A₁) (c : Lv.obj J ⟶ V₁)
    (X : J ⟶ Rt.obj V₁) (s : Lf.obj V₁ ⟶ A₁)
    (hb : aV.unit.app J ≫ Rt.map ε = aT.unit.app J) (hc : aV.unit.app J ≫ Rt.map c = X)
    (hd : @CategoryStruct.comp _ _ (Lf.obj (Lv.obj J)) (Lf.obj (Lt.obj J)) A₁ (Lf.map ε)
        (@CategoryStruct.comp _ _ (Lf.obj (Lt.obj J)) A₂ A₁ g d) = Lf.map c ≫ s) :
    (aT.comp aF).unit.app J ≫ (Rf ⋙ Rt).map (g ≫ d) = X ≫ Rt.map (aF.unit.app V₁ ≫ Rf.map s) := by
  have hn₁ := aF.unit_naturality ε
  have hn₂ := aF.unit_naturality c
  rw [Adjunction.comp_unit_app, ← hb, Functor.comp_map]
  simp only [Category.assoc]
  rw [← Rt.map_comp, ← Rt.map_comp, ← Category.assoc ε, ← hn₁, Category.assoc, ← Rf.map_comp, hd,
    Rf.map_comp, ← Category.assoc, hn₂, Category.assoc, Rt.map_comp, ← Category.assoc, hc]

/-- The transport `F (Lt J) = A₁` after `F` of a transport `V = Lt J`. -/
theorem map_eqToHom_comp_eqToHom_eq {Lt : 𝒜 ⥤ ℬ} {F : ℬ ⥤ 𝒞} {J : 𝒜} {V : ℬ} {A₁ : 𝒞}
    (e : V = Lt.obj J) (ε : V ⟶ Lt.obj J) (hε : ε = eqToHom e) (q : (Lt ⋙ F).obj J = A₁)
    (g : (Lt ⋙ F).obj J ⟶ A₁) (hg : g = eqToHom q) (β : F.obj V = A₁) (s : F.obj V ⟶ A₁)
    (hs : s = eqToHom β) :
    @CategoryStruct.comp _ _ (F.obj V) (F.obj (Lt.obj J)) A₁ (F.map ε) g = s := by
  subst hε hg hs
  simp [eqToHom_map]

/-- `Deformation.ToposThickening.compUnit_comp_map_eq_comp_map_unit_comp` for a transport alone:
the composite unit at `J` followed by `(Rf ⋙ Rt)` of `g` is the unit of `Lv ⊣ Rt` followed by the
unit of `Lf ⊣ Rf` and `s`, provided `s` is `g` after the transport `ε`. -/
theorem compUnit_comp_map_eq_comp_map_unit_comp_of_eq {Lt Lv : 𝒜 ⥤ ℬ} {Rt : ℬ ⥤ 𝒜}
    {Lf : ℬ ⥤ 𝒞} {Rf : 𝒞 ⥤ ℬ} (aT : Lt ⊣ Rt) (aV : Lv ⊣ Rt) (aF : Lf ⊣ Rf) {J : 𝒜} {A₁ : 𝒞}
    (ε : Lv.obj J ⟶ Lt.obj J) (g : (Lt ⋙ Lf).obj J ⟶ A₁) (X : J ⟶ Rt.obj (Lv.obj J))
    (s : Lf.obj (Lv.obj J) ⟶ A₁) (hb : aV.unit.app J ≫ Rt.map ε = aT.unit.app J)
    (hX : aV.unit.app J = X)
    (hd : @CategoryStruct.comp _ _ (Lf.obj (Lv.obj J)) (Lf.obj (Lt.obj J)) A₁ (Lf.map ε) g = s) :
    (aT.comp aF).unit.app J ≫ (Rf ⋙ Rt).map g =
      X ≫ Rt.map (aF.unit.app (Lv.obj J) ≫ Rf.map s) := by
  simpa [hX] using compUnit_comp_map_eq_comp_map_unit_comp aT aV aF ε g (𝟙 A₁) (𝟙 _) X s hb
    (by simp [hX]) (by simpa using hd)

/-- `Deformation.ToposThickening.compUnit_comp_map_eq_comp_map_unit_comp`, with the transpose
along `Lv ⊣ Rt` left unevaluated. -/
theorem compUnit_comp_map_eq_unit_comp_map_comp_unit_comp {Lt Lv : 𝒜 ⥤ ℬ} {Rt : ℬ ⥤ 𝒜}
    {Lf : ℬ ⥤ 𝒞} {Rf : 𝒞 ⥤ ℬ} (aT : Lt ⊣ Rt) (aV : Lv ⊣ Rt) (aF : Lf ⊣ Rf) {J : 𝒜} {V₁ : ℬ}
    {A₂ A₁ : 𝒞} (ε : Lv.obj J ⟶ Lt.obj J) (g : (Lt ⋙ Lf).obj J ⟶ A₂) (d : A₂ ⟶ A₁)
    (c : Lv.obj J ⟶ V₁) (s : Lf.obj V₁ ⟶ A₁)
    (hb : aV.unit.app J ≫ Rt.map ε = aT.unit.app J)
    (hd : @CategoryStruct.comp _ _ (Lf.obj (Lv.obj J)) (Lf.obj (Lt.obj J)) A₁ (Lf.map ε)
        (@CategoryStruct.comp _ _ (Lf.obj (Lt.obj J)) A₂ A₁ g d) = Lf.map c ≫ s) :
    (aT.comp aF).unit.app J ≫ (Rf ⋙ Rt).map (g ≫ d) =
      aV.unit.app J ≫ Rt.map (c ≫ aF.unit.app V₁ ≫ Rf.map s) := by
  rw [compUnit_comp_map_eq_comp_map_unit_comp aT aV aF ε g d c _ s hb rfl hd]
  simp only [Functor.map_comp, Category.assoc]

/-- Moving a map past a natural transformation `G ⟶ L ⋙ K`, then rewriting with a given
equation for `u ≫ G.map (e ≫ d)`. -/
theorem comp_map_comp_app_comp_map_map_comp {G : 𝒜 ⥤ 𝒞} {L : 𝒜 ⥤ ℬ} {K : ℬ ⥤ 𝒞} (σ : G ⟶ L ⋙ K)
    {J Z : 𝒞} {A₀ A₂ A₁ : 𝒜} (u : J ⟶ G.obj A₀) (e : A₀ ⟶ A₂) (d : A₂ ⟶ A₁) (v : J ⟶ G.obj A₁)
    (k : K.obj (L.obj A₁) ⟶ Z) (hR : u ≫ G.map (e ≫ d) = v) :
    (u ≫ G.map e ≫ σ.app A₂) ≫ K.map (L.map d) ≫ k = v ≫ σ.app A₁ ≫ k := by
  rw [← hR]
  have h := σ.naturality d
  simp only [Functor.comp_map] at h
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% h]

/-- Combining two commutative squares across identifications of objects. -/
theorem comp_comp_eq_comp_comp_of_eqToHom {J₂ J₁ T Z₂ Z₁ K₂ K₁ N N' M : 𝒜}
    {x : J₂ ⟶ T} {e : J₂ ⟶ J₁} {γ : J₁ ⟶ T} {s₂ : T ⟶ Z₂} {h₂ : T = Z₂} {m₂ : Z₂ ⟶ N'}
    {k₁ : Z₂ = Z₁} {m : Z₁ ⟶ N} {k₂ : N = N'} {h₁ : T = Z₁} {ι₂ : J₂ ⟶ K₂} {ι₁ : J₁ ⟶ K₁}
    {b : K₂ ⟶ K₁} {u₁ : K₁ ⟶ N} {u₂ : K₂ ⟶ M} {v : M ⟶ N'}
    (hx : x = e ≫ γ) (hs : s₂ = eqToHom h₂) (hm : m₂ = eqToHom k₁ ≫ m ≫ eqToHom k₂)
    (hM : γ ≫ eqToHom h₁ ≫ m = ι₁ ≫ u₁) (hL : e ≫ ι₁ = ι₂ ≫ b)
    (hr : u₂ ≫ v = b ≫ u₁ ≫ eqToHom k₂) :
    x ≫ s₂ ≫ m₂ = ι₂ ≫ u₂ ≫ v := by
  subst hx hs hm
  rw [hr]
  simp only [eqToHom_trans_assoc, Category.assoc]
  rw [reassoc_of% hM, reassoc_of% hL]

/-- A map `I₂ ⟶ I₁` read through isomorphisms `A ≅ I₂` and `B ≅ I₁`, as a map `A ⟶ B`. -/
def homThroughIsos {A B I₂ I₁ : 𝒜} (e₂ : A ≅ I₂) (g : I₂ ⟶ I₁) (e₁ : B ≅ I₁) : A ⟶ B :=
  e₂.hom ≫ g ≫ e₁.inv

end Generic

section Transpose

variable {X : RingedTopos.{v, u, w}} {B : RingedTopos.{vB, uB, wB}}
  {B' : RingedTopos.{vB', uB', wB'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [B.J.HasSheafCompose (forget RingCat.{wB})] [B'.J.HasSheafCompose (forget RingCat.{wB'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{wB} RingCat.{wB})]
  [B'.J.HasSheafCompose (forget₂ CommRingCat.{wB'} RingCat.{wB'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [B.J.HasSheafCompose (forget AddCommGrpCat.{wB})]
  [B'.J.HasSheafCompose (forget AddCommGrpCat.{wB'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify B.J AddCommGrpCat.{wB}] [B.J.WEqualsLocallyBijective AddCommGrpCat.{wB}]
  {t : RingedToposHom B B'} (E : MorphismOfFirstOrderThickenings t) (f : RingedToposHom X B)

omit [X.J.HasSheafCompose (forget AddCommGrpCat)] in
/-- The two spellings of `f^*t^*𝒥`, along `f` read through its first four-field form. -/
theorem pullbackModules_toModulesHom_obj_eq_basePullbackIdeal (ht : FirstOrderThickening t) :
    (pullbackModules f.toModulesHom).obj
        ((pullbackModules t.toRingedToposModulesHom).obj ht.idealOfThickening.I) =
      basePullbackIdeal t f ht := by
  rw [f.toModulesHom_eq_toRingedToposModulesHom]
  rfl

omit [X.J.HasSheafCompose (forget AddCommGrpCat)] in
/-- The two spellings of `f^*t^*𝒥`, from `f^*t^*𝒥` to the pullback along the first four-field
form of `f`. -/
theorem basePullbackIdeal_eq_pullbackModules_toModulesHom_obj (ht : FirstOrderThickening t) :
    basePullbackIdeal t f ht = (pullbackModules f.toModulesHom).obj
        ((pullbackModules t.toRingedToposModulesHom).obj ht.idealOfThickening.I) :=
  (pullbackModules_toModulesHom_obj_eq_basePullbackIdeal f ht).symm

/-- The induced map `t₂^*𝒥₂ ⟶ t₁^*𝒥₁`, transposed along `t₂^* ⊣ t₂_*`. -/
theorem unit_comp_map_pullbackIdealMap :
    (reshapeHom t E.O₂ E.fSharp₂).pullbackAdjPushforwardModulesViaComparison.unit.app
        E.second.idealOfThickening.I ≫
      (RingedToposHom.pushforwardModules (reshapeHom t E.O₂ E.fSharp₂)).map E.pullbackIdealMap =
    (SheafOfModules.restrictScalars (structureRingMap (reshapeHom t E.O₂ E.fSharp₂))).map
      (E.idealMap ≫ E.first.idealToPushforwardPullback) :=
  (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)


/-- **The map `f^*t₂^*𝒥₂ ⟶ f^*t₁^*𝒥₁` induced by `𝒥₂ ⟶ 𝒥₁`**: the pullback along `f` of the
induced map `t₂^*𝒥₂ ⟶ t₁^*𝒥₁`, read through the identification of the pullbacks along the two
four-field forms of `f`. -/
noncomputable def basePullbackIdealMap :
    basePullbackIdeal (reshapeHom t E.O₂ E.fSharp₂) f E.second ⟶ basePullbackIdeal t f E.first :=
  mapTransport (pullbackModules f.toModulesHom)
    (basePullbackIdeal_eq_pullbackModules_toModulesHom_obj f E.second) E.pullbackIdealMap
    (pullbackModules_toModulesHom_obj_eq_basePullbackIdeal f E.first)

omit [X.J.HasSheafCompose (forget AddCommGrpCat)] in
/-- The induced map `f^*t₂^*𝒥₂ ⟶ f^*t₁^*𝒥₁` is `f^*` of the induced map `t₂^*𝒥₂ ⟶ t₁^*𝒥₁`,
across the transports between the two pullbacks along `t₂` and the two spellings of
`f^*t^*𝒥`. -/
theorem pullbackModules_map_eqToHom_comp_eqToHom_comp_basePullbackIdealMap :
    (pullbackModules f.toModulesHom).map (eqToHom (congrArg
        (fun g => (pullbackModules g).obj E.second.idealOfThickening.I)
        (reshapeHom t E.O₂ E.fSharp₂).toModulesHom_eq_toRingedToposModulesHom.symm)) ≫
        ((eqToHom (comp_obj_eq_basePullbackIdeal (reshapeHom t E.O₂ E.fSharp₂) f E.second) :
          (Functor.comp.{max uB' wB', max uB wB, max u w, max (max uB' vB') (wB' + 1),
              max (max uB vB) (wB + 1), max (max u v) (w + 1)}
              (pullbackModules (reshapeHom t E.O₂ E.fSharp₂).toModulesHom)
              (pullbackModules f.toModulesHom)).obj E.second.idealOfThickening.I ⟶ _) ≫
          basePullbackIdealMap E f) =
      (pullbackModules f.toModulesHom).map E.pullbackIdealMap ≫
        eqToHom (pullbackModules_toModulesHom_obj_eq_basePullbackIdeal f E.first) :=
  map_eqToHom_comp_comp_mapTransport
    (congrArg (fun g => (pullbackModules g).obj E.second.idealOfThickening.I)
      (reshapeHom t E.O₂ E.fSharp₂).toModulesHom_eq_toRingedToposModulesHom.symm)
    (eqToHom (congrArg (fun g => (pullbackModules g).obj E.second.idealOfThickening.I)
      (reshapeHom t E.O₂ E.fSharp₂).toModulesHom_eq_toRingedToposModulesHom.symm)) rfl
    (comp_obj_eq_basePullbackIdeal (reshapeHom t E.O₂ E.fSharp₂) f E.second)
    (eqToHom (comp_obj_eq_basePullbackIdeal (reshapeHom t E.O₂ E.fSharp₂) f E.second)) rfl
    (basePullbackIdeal_eq_pullbackModules_toModulesHom_obj f E.second) E.pullbackIdealMap
    (pullbackModules_toModulesHom_obj_eq_basePullbackIdeal f E.first) (basePullbackIdealMap E f) rfl
    (eqToHom (pullbackModules_toModulesHom_obj_eq_basePullbackIdeal f E.first)) rfl

/-- **The induced map `f^*t₂^*𝒥₂ ⟶ f^*t₁^*𝒥₁` on the composite unit**: the composite unit of
`t₂^*f^* ⊣ f_*t₂_*` at `𝒥₂` followed by the induced map is `𝒥₂ ⟶ 𝒥₁ ⟶ t_*t^*𝒥₁` followed by the
unit of `f^* ⊣ f_*`. -/
theorem compUnit_comp_map_eqToHom_comp_basePullbackIdealMap :
    ((RingedToposHom.pullbackAdjPushforwardModules (reshapeHom t E.O₂ E.fSharp₂)).comp
        (RingedToposHom.pullbackAdjPushforwardModules f)).unit.app E.second.idealOfThickening.I ≫
      (Functor.comp.{max u w, max uB wB, max uB' wB', max (max u v) (w + 1),
          max (max uB vB) (wB + 1), max (max uB' vB') (wB' + 1)}
          (RingedToposHom.pushforwardModules f)
          (RingedToposHom.pushforwardModules (reshapeHom t E.O₂ E.fSharp₂))).map
        (eqToHom (comp_obj_eq_basePullbackIdeal (reshapeHom t E.O₂ E.fSharp₂) f E.second) ≫
          basePullbackIdealMap E f) =
      (reshapeHom t E.O₂ E.fSharp₂).pullbackAdjPushforwardModulesViaComparison.unit.app
          E.second.idealOfThickening.I ≫
        (RingedToposHom.pushforwardModules (reshapeHom t E.O₂ E.fSharp₂)).map
          (E.pullbackIdealMap ≫ (RingedToposHom.pullbackAdjPushforwardModules f).unit.app
              ((pullbackModules t.toRingedToposModulesHom).obj E.first.idealOfThickening.I) ≫
            (RingedToposHom.pushforwardModules f).map
              (eqToHom (pullbackModules_toModulesHom_obj_eq_basePullbackIdeal f E.first))) :=
  compUnit_comp_map_eq_unit_comp_map_comp_unit_comp
    (RingedToposHom.pullbackAdjPushforwardModules (reshapeHom t E.O₂ E.fSharp₂))
    (reshapeHom t E.O₂ E.fSharp₂).pullbackAdjPushforwardModulesViaComparison
    (RingedToposHom.pullbackAdjPushforwardModules f) _ _ _ _ _
    (unit_viaComparison_comp_eqToHom (reshapeHom t E.O₂ E.fSharp₂) E.second.idealOfThickening.I)
    (pullbackModules_map_eqToHom_comp_eqToHom_comp_basePullbackIdealMap E f)

/-- **The induced map `𝒥₂ ⟶ t₂_*t^*𝒥₁` on underlying sheaves of sets**: the transpose of the
induced map `t₂^*𝒥₂ ⟶ t^*𝒥₁`, followed by `t₂_*` of any map `c` out of `t^*𝒥₁`, is `𝒥₂ ⟶ 𝒥₁`
followed by the unit `𝒥₁ ⟶ t_*t^*𝒥₁` and `t_*c`. -/
theorem moduleSheafFunctor_map_unit_comp_map_pullbackIdealMap_comp
    {Z : SheafOfModules.{wB} (Stacks.SheafOfModules.Tensor.ringSheaf B.O)}
    (c : (pullbackModules t.toRingedToposModulesHom).obj E.first.idealOfThickening.I ⟶ Z) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf E.O₂)).map
        ((reshapeHom t E.O₂ E.fSharp₂).pullbackAdjPushforwardModulesViaComparison.unit.app
            E.second.idealOfThickening.I ≫
          (RingedToposHom.pushforwardModules (reshapeHom t E.O₂ E.fSharp₂)).map
            (E.pullbackIdealMap ≫ c)) =
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf E.O₂)).map
          ((SheafOfModules.restrictScalars (structureRingMap (reshapeHom t E.O₂ E.fSharp₂))).map
            E.idealMap) ≫
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf B'.O)).map
          (t.pullbackAdjPushforwardModulesViaComparison.unit.app E.first.idealOfThickening.I ≫
            (RingedToposHom.pushforwardModules t).map c) := by
  rw [Functor.map_comp (RingedToposHom.pushforwardModules (reshapeHom t E.O₂ E.fSharp₂)),
    ← Category.assoc, unit_comp_map_pullbackIdealMap,
    ← E.first.restrictScalars_map_idealToPushforwardPullback]
  exact Sheaf.hom_ext_sections fun _ _ => rfl

end Transpose

section Column

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v₂, u₂, w}}
  {S : RingedTopos.{vB, uB, wB}} {S' : RingedTopos.{vB', uB', wB'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w})]
  [S.J.HasSheafCompose (forget RingCat.{wB})] [S'.J.HasSheafCompose (forget RingCat.{wB'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{wB} RingCat.{wB})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{wB'} RingCat.{wB'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wB})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wB'})]
  [HasWeakSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify S.J AddCommGrpCat.{wB}] [S.J.WEqualsLocallyBijective AddCommGrpCat.{wB}]
  [HasSheafify X'.J AddCommGrpCat.{w}]
  (i : RingedToposHom X X') (t : RingedToposHom S S')
  (f : RingedToposHom X S) (f' : RingedToposHom X' S')
  (hi : FirstOrderThickening i) (ht : FirstOrderThickening t)
  (comm : f'.comp i = t.comp f)

/-- The composite unit of `t^*f^* ⊣ f_*t_*` at `𝒥`, read on `f^*t^*𝒥`: the unit
`𝒥 ⟶ t_*t^*𝒥` followed by the unit of `f^* ⊣ f_*`. -/
theorem compUnit_comp_map_eqToHom_comp_obj_eq_basePullbackIdeal :
    ((RingedToposHom.pullbackAdjPushforwardModules t).comp
        (RingedToposHom.pullbackAdjPushforwardModules f)).unit.app ht.idealOfThickening.I ≫
      (Functor.comp.{max u w, max uB wB, max uB' wB', max (max u v) (w + 1),
          max (max uB vB) (wB + 1), max (max uB' vB') (wB' + 1)}
          (RingedToposHom.pushforwardModules f) (RingedToposHom.pushforwardModules t)).map
        (eqToHom (comp_obj_eq_basePullbackIdeal t f ht)) =
      t.pullbackAdjPushforwardModulesViaComparison.unit.app ht.idealOfThickening.I ≫
        (RingedToposHom.pushforwardModules t).map
          ((RingedToposHom.pullbackAdjPushforwardModules f).unit.app
              ((pullbackModules t.toRingedToposModulesHom).obj ht.idealOfThickening.I) ≫
            (RingedToposHom.pushforwardModules f).map
              (eqToHom (pullbackModules_toModulesHom_obj_eq_basePullbackIdeal f ht))) :=
  compUnit_comp_map_eq_comp_map_unit_comp_of_eq (RingedToposHom.pullbackAdjPushforwardModules t)
    t.pullbackAdjPushforwardModulesViaComparison (RingedToposHom.pullbackAdjPushforwardModules f)
    (eqToHom (congrArg (fun g => (pullbackModules g).obj ht.idealOfThickening.I)
      t.toModulesHom_eq_toRingedToposModulesHom.symm))
    (eqToHom (comp_obj_eq_basePullbackIdeal t f ht))
    (t.pullbackAdjPushforwardModulesViaComparison.unit.app ht.idealOfThickening.I)
    (eqToHom (pullbackModules_toModulesHom_obj_eq_basePullbackIdeal f ht))
    (unit_viaComparison_comp_eqToHom t ht.idealOfThickening.I) rfl
    (map_eqToHom_comp_eqToHom_eq (congrArg (fun g => (pullbackModules g).obj ht.idealOfThickening.I)
      t.toModulesHom_eq_toRingedToposModulesHom.symm) _ rfl (comp_obj_eq_basePullbackIdeal t f ht) _
      rfl (pullbackModules_toModulesHom_obj_eq_basePullbackIdeal f ht) _ rfl)

include comm in
/-- **The identification `f^*𝒥 = I` of Situation 08VV, read on the base, through the unit of
`t^* ⊣ t_*`**: the unit `𝒥 ⟶ t_*t^*𝒥`, then `t_*` of the unit of `f^* ⊣ f_*`, then
`t_*f_* = f'_*i_*`, then `f'_*` of the identification and of `I ⊂ O'`, is the structure map of
`f'` on `𝒥 ⊂ O_{ℬ'}`. -/
theorem unit_comp_map_comp_basePullbackIdealIsoIdeal_comp_incl_viaComparison
    (hf' : f'.IsFlat)
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict) :
    (t.pullbackAdjPushforwardModulesViaComparison.unit.app ht.idealOfThickening.I ≫
        (RingedToposHom.pushforwardModules t).map
          ((RingedToposHom.pullbackAdjPushforwardModules f).unit.app
              ((pullbackModules t.toRingedToposModulesHom).obj ht.idealOfThickening.I) ≫
            (RingedToposHom.pushforwardModules f).map
              (eqToHom (pullbackModules_toModulesHom_obj_eq_basePullbackIdeal f ht)))) ≫
        (squarePushforwardComparison i t f f' comm).app (basePullbackIdeal t f ht) ≫
        (RingedToposHom.pushforwardModules f').map
          ((SheafOfModules.restrictScalars (structureRingMap i)).map
            (basePullbackIdealIsoIdeal i t f f' hi ht comm hf' hstrict).hom ≫
            hi.idealOfThickening.incl) =
      ht.idealOfThickening.incl ≫ RingedToposHom.unitStructureMap f' := by
  have h := unit_comp_map_comp_basePullbackIdealIsoIdeal_comp_incl i t f f' hi ht comm hf' hstrict
  rw [← compUnit_comp_map_eqToHom_comp_obj_eq_basePullbackIdeal t f ht]
  simp only [Category.assoc] at h ⊢
  exact h

omit [HasWeakSheafify X'.J AddCommGrpCat] [X'.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasWeakSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasWeakSheafify S.J AddCommGrpCat] [S.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify X'.J AddCommGrpCat] in
include comm in
/-- On underlying sheaves of sets, the comparison `t_*f_* = f'_*i_*` is the identification of the
direct images along the two sides of the square. -/
theorem moduleSheafFunctor_map_squarePushforwardComparison_app
    (A : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).map
        ((squarePushforwardComparison i t f f' comm).app A) =
      eqToHom (congrArg (fun g : RingedToposHom X S' =>
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).obj
          ((RingedToposHom.pushforwardModules g).obj A)) comm.symm) := by
  have h1 : (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).map
      ((RingedToposHom.pushforwardModulesCompIso f t).inv.app A) = eqToHom (show
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).obj
          ((RingedToposHom.pushforwardModules f ⋙ RingedToposHom.pushforwardModules t).obj A) =
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).obj
          ((RingedToposHom.pushforwardModules (t.comp f)).obj A) from rfl) := rfl
  have h2 : (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).map
      ((RingedToposHom.pushforwardModulesCompIso i f').hom.app A) = eqToHom (show
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).obj
          ((RingedToposHom.pushforwardModules (f'.comp i)).obj A) =
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).obj
          ((RingedToposHom.pushforwardModules i ⋙ RingedToposHom.pushforwardModules f').obj A)
          from rfl) := rfl
  rw [squarePushforwardComparison, NatTrans.comp_app, NatTrans.comp_app, Functor.map_comp,
    Functor.map_comp, h1, h2, eqToHom_app, eqToHom_map, eqToHom_trans, eqToHom_trans]
  rfl

include comm in
/--
`Deformation.ToposThickening.unit_comp_map_comp_basePullbackIdealIsoIdeal_comp_incl_viaComparison`
on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_unit_comp_map_comp_eqToHom_comp_map_comp_incl
    (hf' : f'.IsFlat)
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).map
        (t.pullbackAdjPushforwardModulesViaComparison.unit.app ht.idealOfThickening.I ≫
          (RingedToposHom.pushforwardModules t).map
            ((RingedToposHom.pullbackAdjPushforwardModules f).unit.app
                ((pullbackModules t.toRingedToposModulesHom).obj ht.idealOfThickening.I) ≫
              (RingedToposHom.pushforwardModules f).map
                (eqToHom (pullbackModules_toModulesHom_obj_eq_basePullbackIdeal f ht)))) ≫
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).map
        ((squarePushforwardComparison i t f f' comm).app (basePullbackIdeal t f ht)) ≫
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).map
        ((RingedToposHom.pushforwardModules f').map
          ((SheafOfModules.restrictScalars (structureRingMap i)).map
            (basePullbackIdealIsoIdeal i t f f' hi ht comm hf' hstrict).hom ≫
            hi.idealOfThickening.incl)) =
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).map
        ht.idealOfThickening.incl ≫
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).map
        (RingedToposHom.unitStructureMap f') := by
  have h := (Functor.map_comp _ _ _).symm.trans ((congrArg
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf S'.O)).map
    (unit_comp_map_comp_basePullbackIdealIsoIdeal_comp_incl_viaComparison i t f f' hi ht comm hf'
      hstrict)).trans (Functor.map_comp _ _ _))
  rw [Functor.map_comp _ ((squarePushforwardComparison i t f f' comm).app _)] at h
  exact h

include comm in
/-- The reduction `(f')^*𝒥 ⟶ i_*i^*(f')^*𝒥 = i_*f^*𝒥` is an epimorphism: the unit of a first
order thickening is. -/
theorem cancel_homEquiv_eqToHom_comp_basePullbackIdealIsoPullback_inv
    {Z : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)}
    {a b : (RingedToposHom.pushforwardModules i).obj (basePullbackIdeal t f ht) ⟶ Z}
    (h : (RingedToposHom.pullbackAdjPushforwardModules i).homEquiv _ _
        (eqToHom (congrArg (fun g => (pullbackModules g).obj
          ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I))
          i.toModulesHom_eq_toRingedToposModulesHom.symm).symm ≫
          (basePullbackIdealIsoPullback i t f f' hi ht comm).inv) ≫ a =
      (RingedToposHom.pullbackAdjPushforwardModules i).homEquiv _ _
        (eqToHom (congrArg (fun g => (pullbackModules g).obj
          ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I))
          i.toModulesHom_eq_toRingedToposModulesHom.symm).symm ≫
          (basePullbackIdealIsoPullback i t f f' hi ht comm).inv) ≫ b) : a = b := by
  rw [Adjunction.homEquiv_unit, ← unit_viaComparison_comp_eqToHom i _] at h
  simp only [Category.assoc] at h
  have := epi_pullbackAdjPushforward_unit_app hi
    ((pullbackModules f'.toModulesHom).obj ht.idealOfThickening.I)
  rw [cancel_epi, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, cancel_epi] at h
  exact h

end Column

namespace MorphismOfFirstOrderThickenings

section IdealSheaves

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v₂, u₂, wB}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{wB})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{wB} RingCat.{wB})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{wB})]
  {i : RingedToposHom X Y} (D : MorphismOfFirstOrderThickenings i)

/-- **The map `I₂ ⟶ I₁` of a morphism of first order thickenings is `h^♯` on the defining
ideals**, on underlying sheaves of sets: `I₂ ⟶ I₁ ⊂ O'₁` is `I₂ ⊂ O'₂` followed by `h^♯`. -/
theorem moduleSheafFunctor_map_idealMap_comp_incl :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf D.O₂)).map
        ((SheafOfModules.restrictScalars (structureRingMap (reshapeHom i D.O₂ D.fSharp₂))).map
          D.idealMap) ≫
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        D.first.idealOfThickening.incl =
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf D.O₂)).map
        D.second.idealOfThickening.incl ≫
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf D.O₂)).map
        (RingedToposHom.unitStructureMap
          (RingedToposHom.coefficientMorphism (O := D.O₂) (O' := Y.O) Y.J D.hSharp)) := by
  refine Sheaf.hom_ext_sections fun U b => ?_
  have h := congrArg (fun m => (Sheaf.sectionsFunctor Y.J U).map m (D.inclTwo U b))
    (RingedToposHom.forgetRing_map_coefficientMorphism_fSharp Y.J D.hSharp)
  exact (D.inclOne_idealMap U b).trans (h.symm.trans
    (RingedToposHom.unitStructureMap_val_app
      (RingedToposHom.coefficientMorphism (O := D.O₂) (O' := Y.O) Y.J D.hSharp) U
      (D.inclTwo U b)).symm)

/-- The inclusion `I₁ ⊂ O'₁` of the defining ideal of the first thickening, read over `O'₂`: a map
into the direct image of `O'₁` along `h : (Sh(C), O'₁) ⟶ (Sh(C), O'₂)`. -/
noncomputable def idealInclPushforward :
    (SheafOfModules.restrictScalars (structureRingMap (reshapeHom i D.O₂ D.fSharp₂))).obj
        D.first.I ⟶
      (RingedToposHom.pushforwardModules
          (RingedToposHom.coefficientMorphism (O := D.O₂) (O' := Y.O) Y.J D.hSharp)).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  (D.restrictHIso D.first.I).inv ≫
    (SheafOfModules.restrictScalars D.ringMapH).map D.first.idealOfThickening.incl ≫
    (RingedToposHom.coefficientMorphismPushforwardIso D.hSharp).hom.app
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

/-- The inclusion `I₁ ⊂ O'₁` read over `O'₂` is the inclusion on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_idealInclPushforward :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf D.O₂)).map
        D.idealInclPushforward =
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        D.first.idealOfThickening.incl :=
  Sheaf.hom_ext_sections fun _ _ => rfl

/-- **The map `I₂ ⟶ I₁` is `h^♯` on the defining ideals**, as maps of `O'₂`-modules into the
direct image of `O'₁` along `h`. -/
theorem idealMap_comp_idealInclPushforward :
    (SheafOfModules.restrictScalars (structureRingMap (reshapeHom i D.O₂ D.fSharp₂))).map
        D.idealMap ≫ D.idealInclPushforward =
      D.second.idealOfThickening.incl ≫ RingedToposHom.unitStructureMap
        (RingedToposHom.coefficientMorphism (O := D.O₂) (O' := Y.O) Y.J D.hSharp) := by
  apply Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor
  refine (Functor.map_comp _ _ _).trans ?_
  rw [moduleSheafFunctor_map_idealInclPushforward]
  exact (moduleSheafFunctor_map_idealMap_comp_incl D).trans (Functor.map_comp _ _ _).symm

/-- The inclusion `I₁ ⊂ O'₁` read over `O'₂` is a monomorphism: it is injective on sections. -/
theorem cancel_idealInclPushforward
    {M : SheafOfModules.{wB} (Stacks.SheafOfModules.Tensor.ringSheaf D.O₂)}
    {a b : M ⟶ (SheafOfModules.restrictScalars (structureRingMap (reshapeHom i D.O₂ D.fSharp₂))).obj
      D.first.I}
    (h : a ≫ D.idealInclPushforward = b ≫ D.idealInclPushforward) : a = b := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V =>
    ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  exact D.first.injective V (congrArg (fun m => m.val.app V x) h)

end IdealSheaves

end MorphismOfFirstOrderThickenings

section FSharpRing

variable {Y : RingedTopos.{v₂, u₂, w}} {B' : RingedTopos.{vB', uB', wB'}}
  [Y.J.HasSheafCompose (forget RingCat.{w})] [B'.J.HasSheafCompose (forget RingCat.{wB'})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B'.J.HasSheafCompose (forget₂ CommRingCat.{wB'} RingCat.{wB'})]

/-- The structure map along two equal morphisms of ringed topoi, on underlying sheaves of
sets. -/
theorem sheafCompose_map_fSharpRing_eq_of_eq {g g' : RingedToposHom Y B'} (h : g = g') :
    (sheafCompose B'.J (forget RingCat.{wB'})).map g.fSharpRing =
      (sheafCompose B'.J (forget RingCat.{wB'})).map g'.fSharpRing ≫
        eqToHom (congrArg (fun m : RingedToposHom Y B' =>
          (sheafCompose B'.J (forget RingCat.{wB'})).obj
            (Stacks.Sheaves.ToposPushforward.pushforwardRingSheaf m.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) h.symm) := by
  subst h
  simp

end FSharpRing

section OverThickened

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v₂, u₂, w}}
  {B : RingedTopos.{vB, uB, wB}} {B' : RingedTopos.{vB', uB', wB'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [B.J.HasSheafCompose (forget RingCat.{wB})] [B'.J.HasSheafCompose (forget RingCat.{wB'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{wB} RingCat.{wB})]
  [B'.J.HasSheafCompose (forget₂ CommRingCat.{wB'} RingCat.{wB'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [B.J.HasSheafCompose (forget AddCommGrpCat.{wB})]
  [B'.J.HasSheafCompose (forget AddCommGrpCat.{wB'})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [HasWeakSheafify B.J AddCommGrpCat.{wB}] [B.J.WEqualsLocallyBijective AddCommGrpCat.{wB}]

/-- **The map `f^*𝒥₂ ⟶ f^*𝒥₁` induced by `𝒥₂ ⟶ 𝒥₁`**,
`Deformation.ToposThickening.basePullbackIdealMap` read on the thickened topos as a map of modules
over `i_*O`. -/
noncomputable def basePullbackIdealOverThickenedMap (i : RingedToposHom X Y)
    {t : RingedToposHom B B'}
    (E : MorphismOfFirstOrderThickenings t) (f : RingedToposHom X B) :
    basePullbackIdealOverThickened i (reshapeHom t E.O₂ E.fSharp₂) f E.second ⟶
      basePullbackIdealOverThickened i t f E.first :=
  (pushforwardModuleFunctor i.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
    (basePullbackIdealMap E f)

end OverThickened

section TwoColumns

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v₂, u₂, w}}
  {B : RingedTopos.{vB, uB, wB}} {B' : RingedTopos.{vB', uB', wB'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [B.J.HasSheafCompose (forget RingCat.{wB})] [B'.J.HasSheafCompose (forget RingCat.{wB'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{wB} RingCat.{wB})]
  [B'.J.HasSheafCompose (forget₂ CommRingCat.{wB'} RingCat.{wB'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [B.J.HasSheafCompose (forget AddCommGrpCat.{wB})]
  [B'.J.HasSheafCompose (forget AddCommGrpCat.{wB'})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [HasWeakSheafify B.J AddCommGrpCat.{wB}] [B.J.WEqualsLocallyBijective AddCommGrpCat.{wB}]
  {i : RingedToposHom X Y} {t : RingedToposHom B B'}
  (U : MorphismOfFirstOrderThickenings i) (E : MorphismOfFirstOrderThickenings t)
  (f : RingedToposHom X B)
  (f₂ : RingedToposHom (reshape Y U.O₂) (reshape B' E.O₂))
  (r₂ : f₂.comp (reshapeHom i U.O₂ U.fSharp₂) = (reshapeHom t E.O₂ E.fSharp₂).comp f)
  (hf₂ : f₂.IsFlat)
  (hs₂ : (MorphismOfThickenings.ofFirstOrderThickenings (reshapeHom i U.O₂ U.fSharp₂)
    (reshapeHom t E.O₂ E.fSharp₂) f f₂ U.second E.second r₂).IsStrict)
  (f₁ : RingedToposHom Y B')
  (comm : f₂.comp (RingedToposHom.coefficientMorphism (O := U.O₂) (O' := Y.O) Y.J U.hSharp) =
    (RingedToposHom.coefficientMorphism (O := E.O₂) (O' := B'.O) B'.J E.hSharp).comp f₁)

include r₂ in
/-- **The upper map of ideals, transposed along `f'₂`**: the reduction followed by the
identification `f^*𝒥₂ = I₂`, the map `I₂ ⟶ I₁` and `I₁ ⊂ O'₁`, read over `O'₂` and transposed
along `f'₂`, is the structure map of `f'₂` on `𝒥₂` followed by `h^♯`. -/
theorem homEquiv_reduction_comp_map_comp_idealInclPushforward :
    (RingedToposHom.pullbackAdjPushforwardModules f₂).homEquiv _ _
        ((RingedToposHom.pullbackAdjPushforwardModules (reshapeHom i U.O₂ U.fSharp₂)).homEquiv _ _
            (eqToHom (congrArg (fun g => (pullbackModules g).obj
              ((pullbackModules f₂.toModulesHom).obj E.second.idealOfThickening.I))
              (reshapeHom i U.O₂ U.fSharp₂).toModulesHom_eq_toRingedToposModulesHom.symm).symm ≫
              (basePullbackIdealIsoPullback (reshapeHom i U.O₂ U.fSharp₂)
                (reshapeHom t E.O₂ E.fSharp₂) f f₂ U.second E.second r₂).inv) ≫
          (SheafOfModules.restrictScalars (structureRingMap (reshapeHom i U.O₂ U.fSharp₂))).map
            (basePullbackIdealIsoIdeal (reshapeHom i U.O₂ U.fSharp₂) (reshapeHom t E.O₂ E.fSharp₂)
              f f₂ U.second E.second r₂ hf₂ hs₂).hom ≫
          (SheafOfModules.restrictScalars (structureRingMap (reshapeHom i U.O₂ U.fSharp₂))).map
            U.idealMap ≫ U.idealInclPushforward) =
      E.second.idealOfThickening.incl ≫ RingedToposHom.unitStructureMap f₂ ≫
        (RingedToposHom.pushforwardModules f₂).map (RingedToposHom.unitStructureMap
          (RingedToposHom.coefficientMorphism (O := U.O₂) (O' := Y.O) Y.J U.hSharp)) := by
  rw [MorphismOfFirstOrderThickenings.idealMap_comp_idealInclPushforward]
  refine (congrArg _ (Category.assoc _ _ _).symm).trans ?_
  rw [basePullbackIdealReduction_comp_basePullbackIdealIsoIdeal (reshapeHom i U.O₂ U.fSharp₂)
      (reshapeHom t E.O₂ E.fSharp₂) f f₂ U.second E.second r₂ hf₂ hs₂]
  refine (congrArg _ (Category.assoc _ _ _).symm).trans ?_
  exact ((Adjunction.homEquiv_naturality_right _ _ _).trans (congrArg (fun x => x ≫
    (RingedToposHom.pushforwardModules f₂).map (RingedToposHom.unitStructureMap
      (RingedToposHom.coefficientMorphism (O := U.O₂) (O' := Y.O) Y.J U.hSharp)))
    (homEquiv_ofFirstOrderThickenings_idealMap_comp_incl (reshapeHom i U.O₂ U.fSharp₂)
      (reshapeHom t E.O₂ E.fSharp₂) f f₂ U.second E.second r₂))).trans (Category.assoc _ _ _)

include r₂ in
/-- **The induced map `f^*𝒥₂ ⟶ f^*𝒥₁`, transposed along `f'₂`**: the reduction followed by the
direct image of the induced map and of any map `z` out of `i_*f^*𝒥₁`, transposed along `f'₂`, is
`𝒥₂ ⟶ 𝒥₁ ⟶ t_*t^*𝒥₁` (the transpose of the induced map `t₂^*𝒥₂ ⟶ t₁^*𝒥₁`), then `t₂_*` of the
unit of `f^* ⊣ f_*`, then `t₂_*f_* = f'₂_*i₂_*` and `z`. -/
theorem homEquiv_reduction_comp_map_basePullbackIdealMap_comp
    {Z : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (reshape Y U.O₂).O)}
    (z : (RingedToposHom.pushforwardModules (reshapeHom i U.O₂ U.fSharp₂)).obj
      (basePullbackIdeal t f E.first) ⟶ Z) :
    (RingedToposHom.pullbackAdjPushforwardModules f₂).homEquiv _ _
        ((RingedToposHom.pullbackAdjPushforwardModules (reshapeHom i U.O₂ U.fSharp₂)).homEquiv _ _
            (eqToHom (congrArg (fun g => (pullbackModules g).obj
              ((pullbackModules f₂.toModulesHom).obj E.second.idealOfThickening.I))
              (reshapeHom i U.O₂ U.fSharp₂).toModulesHom_eq_toRingedToposModulesHom.symm).symm ≫
              (basePullbackIdealIsoPullback (reshapeHom i U.O₂ U.fSharp₂)
                (reshapeHom t E.O₂ E.fSharp₂) f f₂ U.second E.second r₂).inv) ≫
          (RingedToposHom.pushforwardModules (reshapeHom i U.O₂ U.fSharp₂)).map
            (basePullbackIdealMap E f) ≫ z) =
      ((reshapeHom t E.O₂ E.fSharp₂).pullbackAdjPushforwardModulesViaComparison.unit.app
          E.second.idealOfThickening.I ≫
        (RingedToposHom.pushforwardModules (reshapeHom t E.O₂ E.fSharp₂)).map (E.pullbackIdealMap ≫
          (RingedToposHom.pullbackAdjPushforwardModules f).unit.app
              ((pullbackModules t.toRingedToposModulesHom).obj E.first.idealOfThickening.I) ≫
            (RingedToposHom.pushforwardModules f).map
              (eqToHom (pullbackModules_toModulesHom_obj_eq_basePullbackIdeal f E.first)))) ≫
        (squarePushforwardComparison (reshapeHom i U.O₂ U.fSharp₂) (reshapeHom t E.O₂ E.fSharp₂)
          f f₂ r₂).app (basePullbackIdeal t f E.first) ≫
          (RingedToposHom.pushforwardModules f₂).map z := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    eqToHom_comp_basePullbackIdealIsoPullback_inv_eq_squarePullbackComparison
      (reshapeHom i U.O₂ U.fSharp₂) (reshapeHom t E.O₂ E.fSharp₂) f f₂ U.second E.second r₂,
    Functor.map_comp, ← Category.assoc,
    unit_comp_map_basePullbackIdealReduction (reshapeHom i U.O₂ U.fSharp₂)
      (reshapeHom t E.O₂ E.fSharp₂) f f₂ U.second E.second r₂,
    Functor.map_comp]
  exact comp_map_comp_app_comp_map_map_comp
    (squarePushforwardComparison (reshapeHom i U.O₂ U.fSharp₂) (reshapeHom t E.O₂ E.fSharp₂)
      f f₂ r₂)
    _ (eqToHom (comp_obj_eq_basePullbackIdeal (reshapeHom t E.O₂ E.fSharp₂) f E.second))
    (basePullbackIdealMap E f) _ ((RingedToposHom.pushforwardModules f₂).map z)
    (compUnit_comp_map_eqToHom_comp_basePullbackIdealMap E f)

include comm in
/-- The direct images along `f'₂` and `f'₁` of `I₁ ⊂ O'₁` (read over `O'₂`, respectively over
`O'₁`), after the identification `f^*𝒥₁ = I₁`, agree on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_map_restrictScalars_map_comp_idealInclPushforward
    (r₁ : f₁.comp i = t.comp f) (hf₁ : f₁.IsFlat)
    (hs₁ : (MorphismOfThickenings.ofFirstOrderThickenings i t f f₁ U.first E.first r₁).IsStrict) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf E.O₂)).map
        ((RingedToposHom.pushforwardModules f₂).map
          ((SheafOfModules.restrictScalars (structureRingMap (reshapeHom i U.O₂ U.fSharp₂))).map
            (basePullbackIdealIsoIdeal i t f f₁ U.first E.first r₁ hf₁ hs₁).hom ≫
            U.idealInclPushforward)) =
      eqToHom (congrArg (fun P : Sheaf Y.J (Type w) ⥤ Sheaf B'.J (Type wB') =>
        P.obj ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))).obj
          (basePullbackIdealOverThickened i t f E.first)))
          (congrArg (fun m => m.toToposHom.pushforward) comm)) ≫
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf B'.O)).map
          ((RingedToposHom.pushforwardModules f₁).map
            ((SheafOfModules.restrictScalars (structureRingMap i)).map
              (basePullbackIdealIsoIdeal i t f f₁ U.first E.first r₁ hf₁ hs₁).hom ≫
              U.first.idealOfThickening.incl)) ≫
        eqToHom (congrArg (fun P : Sheaf Y.J (Type w) ⥤ Sheaf B'.J (Type wB') =>
          P.obj ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))
            (congrArg (fun m => m.toToposHom.pushforward) comm).symm) := by
  have hW : (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf U.O₂)).map
      ((SheafOfModules.restrictScalars (structureRingMap (reshapeHom i U.O₂ U.fSharp₂))).map
            (basePullbackIdealIsoIdeal i t f f₁ U.first E.first r₁ hf₁ hs₁).hom ≫
            U.idealInclPushforward) =
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((SheafOfModules.restrictScalars (structureRingMap i)).map
              (basePullbackIdealIsoIdeal i t f f₁ U.first E.first r₁ hf₁ hs₁).hom ≫
              U.first.idealOfThickening.incl) :=
    Sheaf.hom_ext_sections fun _ _ => rfl
  refine (RingedToposHom.moduleSheafFunctor_map_pushforwardModules_map f₂ _).trans ?_
  rw [RingedToposHom.moduleSheafFunctor_map_pushforwardModules_map, hW]
  exact Functor.congr_hom (congrArg (fun m => m.toToposHom.pushforward) comm) _

omit [X.J.HasSheafCompose (forget AddCommGrpCat)] [B.J.HasSheafCompose (forget AddCommGrpCat)]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat] [HasSheafify Y.J AddCommGrpCat]
  [HasWeakSheafify Y.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasWeakSheafify X.J AddCommGrpCat] [HasWeakSheafify B.J AddCommGrpCat]
  [B.J.WEqualsLocallyBijective AddCommGrpCat] in
include comm in
/-- **The left square on structure maps**, on underlying sheaves of sets: the structure map of
`f'₂` followed by `f'₂_*` of `h^♯` is `O_{ℬ'₂} ⟶ O_{ℬ'₁}` followed by the structure map of
`f'₁`, across the identification `f'₂_* = f'₁_*` of the square. -/
theorem moduleSheafFunctor_map_unitStructureMap_comp_map_unitStructureMap :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf E.O₂)).map
        (RingedToposHom.unitStructureMap f₂) ≫
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf E.O₂)).map
        ((RingedToposHom.pushforwardModules f₂).map (RingedToposHom.unitStructureMap
          (RingedToposHom.coefficientMorphism (O := U.O₂) (O' := Y.O) Y.J U.hSharp))) =
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf E.O₂)).map
        (RingedToposHom.unitStructureMap
          (RingedToposHom.coefficientMorphism (O := E.O₂) (O' := B'.O) B'.J E.hSharp)) ≫
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf B'.O)).map
          (RingedToposHom.unitStructureMap f₁) ≫
        eqToHom (congrArg (fun P : Sheaf Y.J (Type w) ⥤ Sheaf B'.J (Type wB') =>
          P.obj ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))
            (congrArg (fun m => m.toToposHom.pushforward) comm).symm) := by
  refine ((congrArg₂ (· ≫ ·) (RingedToposHom.moduleSheafFunctor_map_unitStructureMap f₂)
    ((RingedToposHom.moduleSheafFunctor_map_pushforwardModules_map f₂ _).trans
      (congrArg f₂.toToposHom.pushforward.map
        (RingedToposHom.moduleSheafFunctor_map_unitStructureMap
          (RingedToposHom.coefficientMorphism (O := U.O₂) (O' := Y.O) Y.J U.hSharp))))).trans
    (RingedToposHom.comp_fSharpRing_underlying f₂
      (RingedToposHom.coefficientMorphism (O := U.O₂) (O' := Y.O) Y.J U.hSharp)).symm).trans ?_
  rw [sheafCompose_map_fSharpRing_eq_of_eq comm, RingedToposHom.comp_fSharpRing_underlying,
    RingedToposHom.moduleSheafFunctor_map_unitStructureMap
      (RingedToposHom.coefficientMorphism (O := E.O₂) (O' := B'.O) B'.J E.hSharp),
    RingedToposHom.moduleSheafFunctor_map_unitStructureMap f₁]
  exact Category.assoc _ _ _

include r₂ comm in
/-- **The two columns on underlying sheaves of sets**: `𝒥₂ ⟶ 𝒥₁ ⟶ t_*t^*𝒥₁` followed by the unit
of `f^* ⊣ f_*`, the comparison `t₂_*f_* = f'₂_*i₂_*` and `f'₂_*` of the identification
`f^*𝒥₁ = I₁` and `I₁ ⊂ O'₁`, is the structure map of `f'₂` on `𝒥₂` followed by `h^♯`. -/
theorem moduleSheafFunctor_map_unit_comp_map_comp_squarePushforwardComparison_comp_map
    (r₁ : f₁.comp i = t.comp f) (hf₁ : f₁.IsFlat)
    (hs₁ : (MorphismOfThickenings.ofFirstOrderThickenings i t f f₁ U.first E.first r₁).IsStrict) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf E.O₂)).map
        ((reshapeHom t E.O₂ E.fSharp₂).pullbackAdjPushforwardModulesViaComparison.unit.app
            E.second.idealOfThickening.I ≫
          (RingedToposHom.pushforwardModules (reshapeHom t E.O₂ E.fSharp₂)).map
            (E.pullbackIdealMap ≫
              (RingedToposHom.pullbackAdjPushforwardModules f).unit.app
                  ((pullbackModules t.toRingedToposModulesHom).obj E.first.idealOfThickening.I) ≫
                (RingedToposHom.pushforwardModules f).map
                  (eqToHom (pullbackModules_toModulesHom_obj_eq_basePullbackIdeal f E.first)))) ≫
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf E.O₂)).map
        ((squarePushforwardComparison (reshapeHom i U.O₂ U.fSharp₂) (reshapeHom t E.O₂ E.fSharp₂)
          f f₂ r₂).app (basePullbackIdeal t f E.first)) ≫
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf E.O₂)).map
        ((RingedToposHom.pushforwardModules f₂).map
          ((SheafOfModules.restrictScalars (structureRingMap (reshapeHom i U.O₂ U.fSharp₂))).map
            (basePullbackIdealIsoIdeal i t f f₁ U.first E.first r₁ hf₁ hs₁).hom ≫
            U.idealInclPushforward)) =
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf E.O₂)).map
        E.second.idealOfThickening.incl ≫
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf E.O₂)).map
        (RingedToposHom.unitStructureMap f₂) ≫
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf E.O₂)).map
        ((RingedToposHom.pushforwardModules f₂).map (RingedToposHom.unitStructureMap
          (RingedToposHom.coefficientMorphism (O := U.O₂) (O' := Y.O) Y.J U.hSharp))) := by
  have hM := moduleSheafFunctor_map_unit_comp_map_comp_eqToHom_comp_map_comp_incl i t f f₁
    U.first E.first r₁ hf₁ hs₁
  rw [moduleSheafFunctor_map_squarePushforwardComparison_app] at hM
  exact comp_comp_eq_comp_comp_of_eqToHom
    (moduleSheafFunctor_map_unit_comp_map_pullbackIdealMap_comp E _)
    (moduleSheafFunctor_map_squarePushforwardComparison_app (reshapeHom i U.O₂ U.fSharp₂)
      (reshapeHom t E.O₂ E.fSharp₂) f f₂ r₂ _)
    (moduleSheafFunctor_map_map_restrictScalars_map_comp_idealInclPushforward U E f f₂ f₁ comm r₁
      hf₁ hs₁) hM
    (MorphismOfFirstOrderThickenings.moduleSheafFunctor_map_idealMap_comp_incl E)
    (moduleSheafFunctor_map_unitStructureMap_comp_map_unitStructureMap U E f₂ f₁ comm)

include r₂ comm in
/-- **The two columns**: `𝒥₂ ⟶ 𝒥₁ ⟶ t_*t^*𝒥₁` followed by the unit of `f^* ⊣ f_*`, the comparison
`t₂_*f_* = f'₂_*i₂_*` and `f'₂_*` of the identification `f^*𝒥₁ = I₁` and `I₁ ⊂ O'₁`, is the
structure map of `f'₂` on `𝒥₂` followed by `h^♯`. -/
theorem unit_comp_map_comp_squarePushforwardComparison_comp_map_idealInclPushforward
    (r₁ : f₁.comp i = t.comp f) (hf₁ : f₁.IsFlat)
    (hs₁ : (MorphismOfThickenings.ofFirstOrderThickenings i t f f₁ U.first E.first r₁).IsStrict) :
    ((reshapeHom t E.O₂ E.fSharp₂).pullbackAdjPushforwardModulesViaComparison.unit.app
          E.second.idealOfThickening.I ≫
        (RingedToposHom.pushforwardModules (reshapeHom t E.O₂ E.fSharp₂)).map (E.pullbackIdealMap ≫
          (RingedToposHom.pullbackAdjPushforwardModules f).unit.app
              ((pullbackModules t.toRingedToposModulesHom).obj E.first.idealOfThickening.I) ≫
            (RingedToposHom.pushforwardModules f).map
              (eqToHom (pullbackModules_toModulesHom_obj_eq_basePullbackIdeal f E.first)))) ≫
      (squarePushforwardComparison (reshapeHom i U.O₂ U.fSharp₂) (reshapeHom t E.O₂ E.fSharp₂)
        f f₂ r₂).app (basePullbackIdeal t f E.first) ≫
      (RingedToposHom.pushforwardModules f₂).map
        ((SheafOfModules.restrictScalars (structureRingMap (reshapeHom i U.O₂ U.fSharp₂))).map
          (basePullbackIdealIsoIdeal i t f f₁ U.first E.first r₁ hf₁ hs₁).hom ≫
          U.idealInclPushforward) =
    E.second.idealOfThickening.incl ≫ RingedToposHom.unitStructureMap f₂ ≫
      (RingedToposHom.pushforwardModules f₂).map (RingedToposHom.unitStructureMap
        (RingedToposHom.coefficientMorphism (O := U.O₂) (O' := Y.O) Y.J U.hSharp)) := by
  apply Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor
  refine (Functor.map_comp _ _ _).trans ?_
  refine (congrArg (CategoryStruct.comp _) (Functor.map_comp _ _ _)).trans ?_
  refine Eq.trans ?_ ((Functor.map_comp _ _ _).trans
    (congrArg (CategoryStruct.comp _) (Functor.map_comp _ _ _))).symm
  exact moduleSheafFunctor_map_unit_comp_map_comp_squarePushforwardComparison_comp_map U E f f₂ r₂
    f₁ comm r₁ hf₁ hs₁

include r₂ comm in
/-- **The map `I₂ ⟶ I₁` is the map `f^*𝒥₂ ⟶ f^*𝒥₁` induced by `𝒥₂ ⟶ 𝒥₁`**, through the
identifications `f^*𝒥ₖ = Iₖ` of the two columns (as Stacks 08VT does on ringed spaces). -/
theorem basePullbackIdealIsoIdeal_hom_comp_idealMap
    (r₁ : f₁.comp i = t.comp f) (hf₁ : f₁.IsFlat)
    (hs₁ : (MorphismOfThickenings.ofFirstOrderThickenings i t f f₁ U.first E.first r₁).IsStrict) :
    (basePullbackIdealIsoIdeal (reshapeHom i U.O₂ U.fSharp₂) (reshapeHom t E.O₂ E.fSharp₂) f f₂
        U.second E.second r₂ hf₂ hs₂).hom ≫ U.idealMap =
      basePullbackIdealOverThickenedMap i E f ≫
        (basePullbackIdealIsoIdeal i t f f₁ U.first E.first r₁ hf₁ hs₁).hom := by
  apply U.second.restrictScalarsFullyFaithful.map_injective
  refine (Functor.map_comp _ _ _).trans (Eq.trans ?_ (Functor.map_comp _ _ _).symm)
  apply U.cancel_idealInclPushforward
  rw [Category.assoc, Category.assoc]
  apply cancel_homEquiv_eqToHom_comp_basePullbackIdealIsoPullback_inv
    (reshapeHom i U.O₂ U.fSharp₂) (reshapeHom t E.O₂ E.fSharp₂) f f₂ U.second E.second r₂
  apply ((RingedToposHom.pullbackAdjPushforwardModules f₂).homEquiv _ _).injective
  refine (homEquiv_reduction_comp_map_comp_idealInclPushforward U E f f₂ r₂ hf₂ hs₂).trans ?_
  refine Eq.trans ?_ (homEquiv_reduction_comp_map_basePullbackIdealMap_comp U E f f₂ r₂ _).symm
  exact (unit_comp_map_comp_squarePushforwardComparison_comp_map_idealInclPushforward U E f f₂ r₂
    f₁ comm r₁ hf₁ hs₁).symm

include r₂ comm in
/-- **The map `I₂ ⟶ I₁`, read through the identifications `f^*𝒥ₖ = Iₖ`, is the map
`f^*𝒥₂ ⟶ f^*𝒥₁` induced by `𝒥₂ ⟶ 𝒥₁`** (as Stacks 08VT does on ringed spaces). -/
theorem homThroughIsos_basePullbackIdealIsoIdeal_idealMap
    (r₁ : f₁.comp i = t.comp f) (hf₁ : f₁.IsFlat)
    (hs₁ : (MorphismOfThickenings.ofFirstOrderThickenings i t f f₁ U.first E.first r₁).IsStrict) :
    homThroughIsos (basePullbackIdealIsoIdeal (reshapeHom i U.O₂ U.fSharp₂)
        (reshapeHom t E.O₂ E.fSharp₂) f f₂ U.second E.second r₂ hf₂ hs₂) U.idealMap
        (basePullbackIdealIsoIdeal i t f f₁ U.first E.first r₁ hf₁ hs₁) =
      basePullbackIdealOverThickenedMap i E f := by
  rw [homThroughIsos, ← Category.assoc, basePullbackIdealIsoIdeal_hom_comp_idealMap U E f f₂ r₂ hf₂
    hs₂ f₁ comm r₁ hf₁ hs₁, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end TwoColumns

end Deformation.ToposThickening
